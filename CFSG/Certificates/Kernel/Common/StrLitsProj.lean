module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.StrLits
public meta import CFSG.Certificates.Kernel.Common.StrLits

public section

namespace CFSG.KC.StrLits

open Lean Meta Elab Tactic

meta def strLitsProj (n : Name) (snd : Bool) : TacticM Unit := do
  let some body := (← getConstInfo n).value?
    | throwError "str_lits_proj: `{n}` has no visible definition"
  let body := body.consumeMData
  unless body.isAppOfArity ``Prod.mk 4 do
    throwError "str_lits_proj: expected a pair of strings, found{indentExpr body}"
  let (L, h) ← build (body.getArg! (if snd then 3 else 2)) none
  let proj := mkApp3 (mkConst (if snd then ``Prod.snd else ``Prod.fst) [0, 0]) (mkConst ``String)
    (mkConst ``String) (mkConst n)
  liftMetaTactic1 fun g => do
    let ty ← instantiateMVars (← g.getType)
    let abst ← kabstract ty proj
    unless abst.hasLooseBVars do throwError "str_lits_proj: the component does not occur in the goal"
    let motive := Expr.lam `s (mkConst ``String) abst .default
    let g' ← mkFreshExprSyntheticOpaqueMVar (abst.instantiate1 (mkApp (mkConst ``String.ofList) L))
      (← g.getTag)
    g.assign (mkAppN (mkConst ``of_ofList) #[motive, proj, L, h, g'])
    return some g'.mvarId!

elab "str_lits_fst " c:ident : tactic => do
  strLitsProj (← realizeGlobalConstNoOverloadWithInfo c) false

elab "str_lits_snd " c:ident : tactic => do
  strLitsProj (← realizeGlobalConstNoOverloadWithInfo c) true

end CFSG.KC.StrLits

end
