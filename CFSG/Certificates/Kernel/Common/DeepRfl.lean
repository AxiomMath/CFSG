module

public meta import Lean
meta import all Lean.Shell
public import Lean.CoreM

public section

namespace CFSG.KC.DeepRfl

open Lean Meta Elab Tactic

meta def addDeclDeep (mb : Nat) (x : CoreM Unit) : CoreM Unit := do
  let ctx ← read
  let s ← get
  Lean.Internal.setThreadStackSize (USize.ofNat (mb * 1024 * 1024))
  let t ← IO.asTask (prio := .dedicated) (x.toIO ctx s)
  let r ← IO.wait t
  Lean.Internal.setThreadStackSize (USize.ofNat (8 * 1024 * 1024))
  match r with
  | .ok ((), s') => set s'
  | .error e => throwError m!"{e}"

elab "deep_rfl " depth:num mb:num : tactic => do
  let nm ← Term.mkAuxName `deep_rfl
  liftMetaFinishingTactic fun g => do
    let ty ← instantiateMVars (← g.getType)
    if ty.hasFVar || ty.hasMVar then throwError "deep_rfl: the goal is not closed{indentExpr ty}"
    let some (α, a, _) := ty.eq? | throwError "deep_rfl: the goal is not an equation{indentExpr ty}"
    let u ← getLevel α
    let pf := mkApp2 (mkConst ``Eq.refl [u]) α a
    addDeclDeep mb.getNat <|
        withOptions (fun o => maxRecDepth.set (Elab.async.set o false) depth.getNat) do
      addDecl <| .thmDecl { name := nm, levelParams := [], type := ty, value := pf }
    g.assign (mkConst nm)

end CFSG.KC.DeepRfl
