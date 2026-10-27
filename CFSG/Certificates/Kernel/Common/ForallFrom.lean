module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.ForallChunks

open Lean Elab Command Meta in
elab "#kc_forall_from " nm:ident p:term:max n:num pre:ident lo:num : command => do
  let natT := mkConst ``Nat
  liftTermElabM do
    let P ← Term.elabTerm p (some (mkForall `k .default natT (mkSort .zero)))
    Term.synthesizeSyntheticMVarsNoPostponing
    let P ← instantiateMVars P
    if P.hasMVar || P.hasFVar then throwError "#kc_forall_from: the predicate is not closed"
    let n := n.getNat
    let base := pre.getId
    let env ← getEnv
    let mut pf := mkApp (mkConst ``CFSG.KC.ForallChunks.forall_lt_zero) P
    for k in [0:n] do
      let t := base.appendAfter s!"{lo.getNat + k}"
      unless env.contains t do throwError "#kc_forall_from: unknown theorem {t}"
      pf := mkAppN (mkConst ``CFSG.KC.ForallChunks.forall_lt_succ)
        #[P, mkRawNatLit k, pf, mkConst t]
    let ltE := mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, .bvar 0, mkRawNatLit n]
    let ty := mkForall `k .default natT (mkForall `h .default ltE (mkApp P (.bvar 1)).headBeta)
    let name := (← getCurrNamespace) ++ nm.getId
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := pf }
