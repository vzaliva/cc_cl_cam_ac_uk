(*
Very simple inline expander
Only dares to expand applications if operand is value, in order to avoid side effects,
so it in practice mostly does constant propagation 

Could support complex operands with a imperative style variable binding,
However currently variable binding is done by creating a new function, 
which defeats the purpose of function inling 

Could also try to evaluate operations as well to get more complete constant folding

Made in front-end due to easy access to whether functions are recursive or not
probably would be better to implement it backend, 
but that would require reanalysing functions for recursion

Works in 3 phases:
Expand non-recursive function calls to lambdas,
Apply immutable operands to lambdas and inline then
Contract remaining lambdas to function calls

*)
let rec propagate f = function 
    | Ast.UnaryOp(op, e)   -> Ast.UnaryOp(op, f e)
    | Ast.Op(e1, op, e2)   -> Ast.Op(f e1, op, f e2)
    | Ast.If(e1, e2, e3)   -> Ast.If(f e1, f e2, f e3)
    | Ast.Pair(e1, e2)     -> Ast.Pair(f e1, f e2)
    | Ast.Fst e            -> Ast.Fst (f e)
    | Ast.Snd e            -> Ast.Snd (f e)
    | Ast.Inl e            -> Ast.Inl (f e)
    | Ast.Inr e            -> Ast.Inl (f e)
    | Ast.Lambda(x, e)     -> Ast.Lambda(x, f e)
    | Ast.App(e1, e2)      -> Ast.App(f e1, f e2)
    | Ast.Seq el           -> Ast.Seq (propagateList f el)
    | Ast.While (e1, e2)   -> Ast.While (f e1, f e2)
    | Ast.Ref e            -> Ast.Ref (f e)
    | Ast.Deref e          -> Ast.Deref (f e)
    | Ast.Assign (e1, e2)  -> Ast.Assign (f e1, f e2)
    | Ast.LetFun(g, (x, e1), e2)      -> Ast.LetFun(g, (x, f e1), f e2)
    | Ast.LetRecFun(g, (x, e1), e2)   -> Ast.LetRecFun(g, (x, f e1), f e2)
    | Ast.Case(e, (x1, e1), (x2, e2)) -> Ast.Case(f e, (x1, f e1), (x2, f e2))
    | other -> other

and propagateList f = function 
    | [] -> []
    | e::el   -> (propagate f e)::(propagateList f el)


let rec varToExpr x expr = function
    (*Replace var(x) with expr*)
    | Ast.Var(y) when (x=y)                           -> expr
    (*variable got new value, dont continue*)
    | Ast.Lambda(y, e)              when(y=x)         -> Ast.Lambda(y, e) 
    | Ast.LetFun(f, (y, e1), e2)    when (f=x)||(y=x) -> Ast.LetFun(f, (y, e1), e2)
    | Ast.LetRecFun(f, (y, e1), e2) when (f=x)||(y=x) -> Ast.LetRecFun(f, (y, e1), e2)

    | other                                           -> propagate (varToExpr x expr) other
  
let rec exprToVar x expr = function
    (* Replaces expr with var(x), and returns a tuple of the result and boolean 
    whether any replacements were made *)
    | e when (e=expr)                                 -> (Ast.Var(x), true)
    (*variable got new value, dont continue*)
    | Ast.Lambda(y, e)              when (y=x)        -> (Ast.Lambda(x, e), false) 
    | Ast.LetFun(f, (y, e1), e2)    when (f=x)||(y=x) -> (Ast.LetFun(f, (y, e1), e2), true)
    | Ast.LetRecFun(f, (y, e1), e2) when (f=x)||(y=x) -> (Ast.LetRecFun(f, (y, e1), e2), true)

    (*propagation*)
    | Ast.UnaryOp(op, e) -> 
      let (e', r) = exprToVar x expr e in 
      (Ast.UnaryOp(op, e'), r)

    | Ast.Op(e1, op, e2) -> 
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.Op(e1', op, e2'), r1 || r2)

    | Ast.If(e1, e2, e3) -> 
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      let (e3', r3) = exprToVar x expr e3 in
      (Ast.If(e1', e2', e3'), (r1 || r2 || r3))

    | Ast.Pair(e1, e2) ->       
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.Pair(e1', e2'), r1 || r2)

    | Ast.Fst e -> 
      let (e', r) = exprToVar x expr e in 
      (Ast.Fst e', r)

    | Ast.Snd e -> 
      let (e', r) = exprToVar x expr e in 
      (Ast.Snd e', r)

    | Ast.Inl e ->  
      let (e', r) = exprToVar x expr e in 
      (Ast.Inl e', r)

    | Ast.Inr e ->  
      let (e', r) = exprToVar x expr e in 
      (Ast.Inr e', r)

    | Ast.Lambda(y, e) ->  
      let (e', r) = exprToVar x expr e in 
      (Ast.Lambda(y, e'), r)

    | Ast.App(e1, e2) ->        
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.App(e1', e2'), r1 || r2)

    | Ast.Seq el -> 
      let (el', r) = exprToVarList x expr el in 
      (Ast.Seq el', r)

    | Ast.While (e1, e2) -> 
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.While(e1', e2'), r1 || r2)

    | Ast.Ref e -> 
      let (e', r) = exprToVar x expr e in 
      (Ast.Ref e', r)

    | Ast.Deref e -> 
      let (e', r) = exprToVar x expr e in 
      (Ast.Deref e', r)

    | Ast.Assign (e1, e2) ->        
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.Assign(e1', e2'), r1 || r2)

    | Ast.LetFun(f, (y, e1), e2) ->        
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.LetFun(f, (y, e1'), e2'), r1 || r2)

    | Ast.LetRecFun(f, (y, e1), e2) -> 
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.LetRecFun(f, (y, e1'), e2'), r1 || r2)

    | Ast.Case(e, (x1, e1), (x2, e2)) -> 
      let (e1', r1) = exprToVar x expr e1 in
      let (e2', r2) = exprToVar x expr e2 in
      (Ast.Case(e, (x1, e1'), (x2, e2')), r1 || r2)

    | other -> (other, false)

and exprToVarList x expr = function
    | [] -> ([], false)
    | e::el -> 
      let (e', r1) = exprToVar x expr e in
      let (el', r2) = exprToVarList x expr el in
      (e'::el', r1 || r2)


let rec isImmutable = function
    | Ast.Integer n   -> true
    | Ast.Boolean b   -> true
    | Ast.Unit        -> true
    | Ast.Pair(e1, e2)-> (isImmutable e1) && (isImmutable e2)
    | Ast.Inl e       -> isImmutable e
    | Ast.Inr e       -> isImmutable e
    | Ast.Lambda(x, e)-> true
    | other           -> false

let rec lambdaExpand = function
  (* replace occurences of functions with their lambda *)
  (* Keeps the LetFun statement to remember where functions was defined for contracting,
     This Letfun gets in the way of some applications, for example function g in example/closure_add.slang.
     Some other way of remembering where functions were defined would be more effective
  *)
    | Ast.LetFun(f, (x, e1), e2) -> 
        let e1' = lambdaExpand e1 in
        let e2' = lambdaExpand (varToExpr f (Lambda(x, e1')) e2) in
        Ast.LetFun(f, (x, e1'), e2')
    | other -> propagate lambdaExpand other

let rec valueApply = function
    (* Inline lambda applications, if operand is immutable *)
    | Ast.App(e1, e2) ->
        let e1' = valueApply e1 in
        let e2' = valueApply e2 in
        (match e1' with
            | Ast.Lambda(x, e3) when (isImmutable e2') -> valueApply (varToExpr x e2' e3)
            | nonApplicable -> Ast.App(e1', e2')
        )
    | other -> propagate valueApply other

let rec lambdaContract = function
    | Ast.LetFun(f, (x, e1), e2) ->
        let (e2', r) = exprToVar f (Lambda(x, e1)) e2 in
        if r then
          Ast.LetFun(f, (x, lambdaContract e1), lambdaContract e2')
        else (* No references to f left, we can remove function block*)
          lambdaContract e2'
    | other -> propagate lambdaContract other
