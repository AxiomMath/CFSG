module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree

public section

open Lean Elab Command Meta

elab "#kc_forall_tree_from " nm:ident p:term:max lo:num n:num pre:ident : command => do
  let natT := mkConst ``Nat
  liftTermElabM do
    let P ← Term.elabTerm p (some (mkForall `k .default natT (mkSort .zero)))
    Term.synthesizeSyntheticMVarsNoPostponing
    let P ← instantiateMVars P
    if P.hasMVar || P.hasFVar then throwError "#kc_forall_tree_from: the predicate is not closed"
    let lo := lo.getNat
    let n := n.getNat
    if n = 0 then throwError "#kc_forall_tree_from: n = 0"
    let base := pre.getId
    let env ← getEnv
    for k in [0:n] do
      let t := base.appendAfter s!"{lo + k}"
      unless env.contains t do throwError "#kc_forall_tree_from: unknown theorem {t}"
    let addE := mkAppN (mkConst ``HAdd.hAdd [0, 0, 0])
      #[natT, natT, natT, mkApp2 (mkConst ``instHAdd [0]) natT (mkConst ``instAddNat)]
    let Q := mkLambda `k .default natT (mkApp P (mkApp2 addE (mkRawNatLit lo) (.bvar 0)))
    let pf := CFSG.KC.ForallTree.build base Q lo n
    let ltE := mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, .bvar 0, mkRawNatLit n]
    let ty := mkForall `k .default natT (mkForall `h .default ltE (mkApp Q (.bvar 1)).headBeta)
    let name := (← getCurrNamespace) ++ nm.getId
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := pf }

end
