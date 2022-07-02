/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System.IO;
using System.Collections.Generic;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        public Expression StmtWLP(Expression e, Statement s)
        {
            if (s is AssumeStatement)
            {
                AssumeStatement ass = (AssumeStatement)s;
                e = new ImplicationExpression(ass.condition, e);
            }
            else if (s is AssertStatement)
            {
                AssertStatement ass = (AssertStatement)s;
                e = new AndExpression(e, ass.pred);
            }
            else if (s is VariableAssignStatement)
            {
                VariableAssignStatement vas = (VariableAssignStatement)s;
                e = e.Substitute(vas.variable, vas.rhs);
            }
            else if (s is SubscriptAssignStatement)
            {
                SubscriptAssignStatement sas = (SubscriptAssignStatement)s;
                VariableExpression array = new VariableExpression(sas.array);
                VariableExpression length = new VariableExpression(sas.array.length);
                Expression tmp = new ArrayUpdateExpression(array, sas.subscript, sas.rhs, length);
                e = e.Substitute(sas.array, tmp);
            }
            else if (s is FunctionCallStatement)
            {
                FunctionCallStatement fcs = (FunctionCallStatement)s;
                List<Expression> post_conditions = fcs.rhs.function.postconditionBlock.conditions;
                Expression tmp = GetAndExpression(post_conditions);
  
                for (int i = 0; i < fcs.rhs.argumentVariables.Count; i++)
                {
                    VariableExpression sub = new VariableExpression(fcs.rhs.argumentVariables[i]);
                    tmp = tmp.Substitute(fcs.rhs.function.parameters[i], sub);
                }
                for (int i = 0; i < fcs.lhs.Count; i++)
                {
                    VariableExpression sub = new VariableExpression(fcs.lhs[i]);
                    tmp = tmp.Substitute(fcs.rhs.function.rvs[i], sub);
                }
                e = new ImplicationExpression(tmp, e);
                List<Expression> pre_conditions = fcs.rhs.function.preconditionBlock.conditions;
                Expression tmp2 = GetAndExpression(pre_conditions);

                for (int i = 0; i < fcs.rhs.argumentVariables.Count; i++)
                {
                    VariableExpression sub = new VariableExpression(fcs.rhs.argumentVariables[i]);
                    tmp2 = tmp2.Substitute(fcs.rhs.function.parameters[i], sub);
                }
                e = new AndExpression(tmp2, e);
            }
            return e;
        }
        public Expression BlockWLP(Expression e, Block b)
        {
            LinkedListNode<Statement> curr_s_node = b.statements.Last;
            while(curr_s_node != null)
            {
                e = StmtWLP(e, curr_s_node.Value);
                curr_s_node = curr_s_node.Previous;
            }
            return e;
        }

        public Expression PathWLP(Expression e, LinkedList<Block> path)
        {
            LinkedListNode<Block> curr_b_node = path.Last;
            while(curr_b_node != path.First)
            {
                e = BlockWLP(e, curr_b_node.Value);
                curr_b_node = curr_b_node.Previous;
            }
            Block fb = path.First.Value;
            if (fb is PreconditionBlock)
            {
                PreconditionBlock precon = (PreconditionBlock)fb;
                Expression tmp = GetAndExpression(precon.conditions);
                e = new ImplicationExpression(tmp, e);
            }
            else if (fb is LoopHeadBlock)
            {
                LoopHeadBlock loop = (LoopHeadBlock)fb;
                e = BlockWLP(e, loop);
                Expression tmp = GetAndExpression(loop.invariants);
                e = new ImplicationExpression(tmp, e);
            }
            return e;
        }

        public bool VerifyWLP(LinkedList<Block> lb)
        {
            LinkedList<Block> path = new LinkedList<Block>(lb);
            Block end = path.Last.Value;
            Expression start;
            path.RemoveLast();
            if (end is PostconditionBlock)
            {
                PostconditionBlock post = (PostconditionBlock)end;
                start = GetAndExpression(post.conditions);
            }
            else
            {
                LoopHeadBlock loop = (LoopHeadBlock)end;
                start = GetAndExpression(loop.invariants);
            }
            start = PathWLP(start, path);

            return (solver.CheckValid(start) == null);
        }

        public bool VerifyRankFuncFromPos(int pos, LinkedList<Block> lb, List<Expression> le)
        {
            List<Expression> rank = new List<Expression>(le);
            LinkedList<Block> path = new LinkedList<Block>(lb);
            Block first = path.First.Value;
            List<Expression> pre = default!;
            if (first is LoopHeadBlock)
            {
                LoopHeadBlock loop = (LoopHeadBlock)first;
                pre = new List<Expression>(loop.rankingFunctions);

            }
            else
            {
                PreconditionBlock p = (PreconditionBlock)first;
                pre = new List<Expression> (p.rankingFunctions);
            }
            
            HashSet<LocalVariable> visited_set = new HashSet<LocalVariable>();
            HashSet<LocalVariable> new_visited_set = new HashSet<LocalVariable>();
            foreach (Expression e in pre)
            {
                visited_set.UnionWith(e.GetFreeVariables());
            }

            Dictionary<LocalVariable, LocalVariable> map = new Dictionary<LocalVariable, LocalVariable>();
            Dictionary<LocalVariable, LocalVariable> r_map = new Dictionary<LocalVariable, LocalVariable>();

            foreach (LocalVariable e in visited_set)
            {
                LocalVariable lv = new LocalVariable();
                lv.name = "new" + e.name;
                lv.type = e.type;
                new_visited_set.Add(lv);
                map.Add(e, lv);
                r_map.Add(lv, e);
            }
            int num = pre.Count;
            for (int i = 0; i < num; i++)
            {
                foreach (LocalVariable v in visited_set)
                {
                    VariableExpression e = new VariableExpression(map[v]);
                    pre[i] = pre[i].Substitute(v, e);
                }
            }
            Expression start = new BoolConstantExpression(false);
            for (int i = 0; i < num; i++)
            {
                Expression tmp = new BoolConstantExpression(true);
                for (int j = 0; j < i; j++)
                {
                    EQExpression eq = new EQExpression(rank[j], pre[j]);
                    tmp = new AndExpression(tmp, eq);
                }
                LTExpression lt = new LTExpression(rank[i], pre[i]);
                tmp = new AndExpression (tmp, lt);
                start = new OrExpression(start, tmp);
            }
            if (pos == -3)
            {
                start = PathWLP(start, path);
            }
            else 
            {
                Block curr_block = path.Last.Value;
                int n = curr_block.statements.Count;
                LinkedListNode<Statement> curr_s_node = curr_block.statements.Last;
                for (int i = 0; i < n; i++)
                {
                    Statement curr_stmt = curr_s_node.Value;
                    curr_s_node = curr_s_node.Previous;
                    if (i <= pos)
                    {
                        continue;
                    }
                    start = StmtWLP(start, curr_stmt);
                }
                path.RemoveLast();
                start = PathWLP(start, path);
            }

            foreach (LocalVariable v in new_visited_set)
            {
                VariableExpression e = new VariableExpression(r_map[v]);
                start = start.Substitute(v, e);
            }
            
            bool result = (solver.CheckValid(start) == null);
            return result;
        }
        public bool VerifyRankFunc(LinkedList<Block> path)
        {
            List<Expression> rank;
            int start = -1;
            while (true)
            {
                (start, path, rank) = StartPos(start, path);
                if (start == -2)
                {
                    return true;
                }
                if (!VerifyRankFuncFromPos(start, path, rank))
                {
                    return false;
                }
            }
        }

        public (int, LinkedList<Block>, List<Expression>) GetPos(LinkedList<Block> path)
        {
            List<Expression> rank = default!;
            while (true)
            {
                path.RemoveLast();
                if (path.Count == 1)
                {
                    return (-2, path, rank);
                }
                Block curr_block = path.Last.Value;
                int num = curr_block.statements.Count;
                LinkedListNode<Statement> curr_s_node = curr_block.statements.Last;
                for (int i = 0; i < num; i++)
                {
                    Statement curr_stmt = curr_s_node.Value;
                    curr_s_node = curr_s_node.Previous;
                    if (curr_stmt is FunctionCallStatement)
                    {
                        FunctionCallStatement fcs = (FunctionCallStatement)curr_stmt;
                        rank = new List<Expression> (fcs.rhs.function.preconditionBlock.rankingFunctions);
                        for (int j = 0; j < fcs.rhs.argumentVariables.Count; j++)
                        {
                            VariableExpression sub = new VariableExpression(fcs.rhs.argumentVariables[j]);
                            int n = rank.Count;
                            for (int k = 0; k < n; k++)
                            {
                                rank[k] = rank[k].Substitute(fcs.rhs.function.parameters[j], sub);
                            }
                        }
                        return (i, path, rank);
                    }
                    else
                    {
                        continue;
                    }
                }
            }
        }
        public (int, LinkedList<Block>, List<Expression>) StartPos(int pos, LinkedList<Block> path)
        {
            Block end = path.Last.Value;
            List<Expression> rank = default!;

            if (pos == -1)
            {
                if (end is PostconditionBlock)
                {
                    return GetPos(path);
                }
                else if (end is LoopHeadBlock)
                {
                    LoopHeadBlock loop = (LoopHeadBlock)end;
                    rank = loop.rankingFunctions;
                    pos = -3;
                    path.RemoveLast();
                    return (pos, path, rank);
                }
            }
            else if (pos >= 0 || pos == -3)
            {
                if (end is BasicBlock)
                {
                    BasicBlock curr_block = (BasicBlock)end;
                    int num = curr_block.statements.Count;
                    LinkedListNode<Statement> curr_s_node = curr_block.statements.Last;
                    for (int i = 0; i < num; i++)
                    {
                        Statement curr_stmt = curr_s_node.Value;
                        curr_s_node = curr_s_node.Previous;
                        if (i <= pos)
                        {
                            continue;
                        }
                        if (curr_stmt is FunctionCallStatement)
                        {
                            FunctionCallStatement fcs = (FunctionCallStatement)curr_stmt;
                            rank = new List<Expression> (fcs.rhs.function.preconditionBlock.rankingFunctions);
                            for (int j = 0; j < fcs.rhs.argumentVariables.Count; j++)
                            {
                                int n = rank.Count;
                                VariableExpression sub = new VariableExpression(fcs.rhs.argumentVariables[j]);
                                for (int k = 0; k < n; k++)
                                {
                                    rank[k] = rank[k].Substitute(fcs.rhs.function.parameters[j], sub);
                                }
                            }
                            return (i, path, rank);
                        }
                    }
                    return GetPos(path);
                }
                else if (end is PreconditionBlock)
                {
                    return (-2, path, rank);
                }
            }
            return (pos, path, rank);
        }

        public int VCAlgo(LinkedListNode<Function> curr)
        {
            IntConstantExpression zero = new IntConstantExpression(0);
            bool rank_flag = (curr.Value.preconditionBlock.rankingFunctions.Count > 0);
            while (curr != null)
            {
                HashSet<string> visited_set = new HashSet<string>();
                Function f = curr.Value;

                if (rank_flag)
                {
                    List<Expression> geList = new List<Expression>();
                    foreach(Expression rf in f.preconditionBlock.rankingFunctions)
                    {
                        geList.Add(new GEExpression(rf, zero));
                    }
                    Expression ge_and = GetAndExpression(geList);
                    ImplicationExpression non_neg = new ImplicationExpression(GetAndExpression(f.preconditionBlock.conditions), ge_and);
                    bool res = (solver.CheckValid(non_neg) == null);
                    if (!res)
                    {
                        return -1;
                    }
                }
                
                Queue<Block> node = new Queue<Block>();
                Queue<LinkedList<Block>> paths = new Queue<LinkedList<Block>>();
                node.Enqueue(f.preconditionBlock);
                LinkedList<Block> path = new LinkedList<Block>();
                path.AddLast(f.preconditionBlock);
                paths.Enqueue(path);
                while (node.Count > 0)
                {
                    Block curr_block = node.Dequeue();
                    LinkedList<Block> curr_path = paths.Dequeue();
                    if (curr_block is LoopHeadBlock || curr_block is PostconditionBlock)
                    {
                        if (!VerifyWLP(curr_path))
                        {
                            return -1;
                        }
                        
                        if (rank_flag)
                        {
                            if (curr_block is LoopHeadBlock)
                            {
                                LoopHeadBlock tmp = (LoopHeadBlock)curr_block;
                                List<Expression> geList = new List<Expression>();
                                foreach(Expression rf in tmp.rankingFunctions)
                                {
                                    geList.Add(new GEExpression(rf, zero));
                                }
                                Expression ge_and = GetAndExpression(geList);
                                ImplicationExpression non_neg = new ImplicationExpression(GetAndExpression(tmp.invariants), ge_and);
                                if (solver.CheckValid(non_neg) != null)
                                {
                                    return -1;
                                }
                            }
                            if (!VerifyRankFunc(curr_path))
                            {
                                return -1;
                            }
                        }
                        if (!visited_set.Contains(curr_block.ToString()))
                        {
                            foreach (Block b in curr_block.successors)
                            {
                                node.Enqueue(b);
                                LinkedList<Block> newPath = new LinkedList<Block>();
                                newPath.AddLast(curr_block);
                                newPath.AddLast(b);
                                paths.Enqueue(newPath);
                            }
                        }
                        visited_set.Add(curr_block.ToString());
                    }
                    else
                    {
                        foreach (Block b in curr_block.successors)
                        {
                            node.Enqueue(b);
                            LinkedList<Block> newPath = new LinkedList<Block>();
                            foreach (Block block in curr_path)
                            {
                                newPath.AddLast(block);
                            }
                            newPath.AddLast(b);
                            paths.Enqueue(newPath);
                        }
                    }
                }
                curr = curr.Next;
            }
            return 1;
        }

        public Expression GetAndExpression(List<Expression> expressions)
        {
            Expression res = new BoolConstantExpression(true);;
            foreach(Expression e in expressions)
            {
                res = new AndExpression(res, e);
            }
            return res;
        }

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        public int Apply(IRMain cfg)
        {
            foreach (Predicate p in cfg.predicates)
            {
                solver.definePredicate(p);
            }
            return VCAlgo(cfg.functions.First);
        }
    }
}