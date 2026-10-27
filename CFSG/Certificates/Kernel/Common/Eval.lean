module

public meta import Lean
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KC.Eval

inductive Val where
  | nat (v : Nat)
  | list (xs : Array Val)
  | ref (n : Name)
  deriving Inhabited

abbrev Step := Array Val → Except String (Array (Name × Val))

end CFSG.KC.Eval

end

namespace CFSG.KC.Eval

meta partial def readExpr (e : Expr) : CoreM Val := do
  match e with
  | .lit (.natVal v) => return .nat v
  | .const n _ => readConst n
  | .mdata _ e => readExpr e
  | _ =>
    let mut e := e
    let mut xs : Array Val := #[]
    repeat
      if e.isAppOfArity ``List.cons 3 then
        xs := xs.push (← readExpr (e.getArg! 1))
        e := e.getArg! 2
      else if e.isAppOfArity ``List.nil 1 then
        return .list xs
      else if e.isAppOfArity ``OfNat.ofNat 3 then
        return ← readExpr (e.getArg! 1)
      else
        throwError "#kc_eval: cannot read {e}"
    return .list xs
where
  readConst (n : Name) : CoreM Val := do
    match (← getConstInfo n).value? (allowOpaque := true) with
    | some v => readExpr v
    | none => throwError "#kc_eval: {n} has no value"

meta partial def valType (pre : Name) (v : Val) : CoreM Expr := do
  match v with
  | .nat _ => return mkConst ``Nat
  | .ref m => return (← getConstInfo (pre ++ m)).type
  | .list xs =>
    let t ← if h : 0 < xs.size then valType pre xs[0] else pure (mkConst ``Nat)
    return mkApp (mkConst ``List [0]) t

meta partial def valExpr (pre : Name) (v : Val) : CoreM Expr := do
  match v with
  | .nat n => return mkRawNatLit n
  | .ref m => return mkConst (pre ++ m)
  | .list xs =>
    let t ← if h : 0 < xs.size then valType pre xs[0] else pure (mkConst ``Nat)
    let mut acc := mkApp (mkConst ``List.nil [0]) t
    for x in xs.reverse do
      acc := mkApp3 (mkConst ``List.cons [0]) t (← valExpr pre x) acc
    return acc

meta def addVal (pre name : Name) (v : Val) : CoreM Unit := do
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type := ← valType pre v, value := ← valExpr pre v,
      hints := .regular 0, safety := .safe }

end CFSG.KC.Eval

declare_syntax_cat kcEvalArg
syntax num : kcEvalArg
syntax ident : kcEvalArg

open CFSG.KC.Eval in
elab "#kc_eval " pre:ident out:ident f:ident args:kcEvalArg* : command => do
  let P := pre.getId
  let X := P ++ out.getId
  let fN ← liftCoreM <| realizeGlobalConstNoOverload f
  let step ← liftTermElabM <| unsafe evalConst Step fN
  liftCoreM <| withOptions (Elab.async.set · false) do
    let t0 ← IO.monoNanosNow
    let mut vs : Array Val := #[]
    for a in args do
      match a with
      | `(kcEvalArg| $n:num) => vs := vs.push (.nat n.getNat)
      | `(kcEvalArg| $i:ident) =>
        let n := if (← getEnv).contains (P ++ i.getId) then P ++ i.getId else i.getId
        vs := vs.push (← readExpr.readConst n)
      | _ => throwError "#kc_eval: bad argument"
    let t1 ← IO.monoNanosNow
    match step vs with
    | .error e => throwError "#kc_eval {X}: {e}"
    | .ok outs =>
      let t2 ← IO.monoNanosNow
      for (n, v) in outs do
        addVal X (X ++ n) v
      let t3 ← IO.monoNanosNow
      let ms (a b : Nat) : Float := (b - a).toFloat / 1e6
      logInfo m!"EVALTIME {X} read {ms t0 t1} step {ms t1 t2} add {ms t2 t3} ms"
