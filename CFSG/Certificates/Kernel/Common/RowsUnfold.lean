module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.EachUnfold
meta import all CFSG.Certificates.Kernel.Common.EachUnfold

open Lean Elab Command Meta

syntax "#kc_rows_unfold " ident num " as " ident " names " ident (" eval" (ppSpace ident)+)? :
  command

open CFSG.KC.EachUnfold in
elab_rules : command
  | `(#kc_rows_unfold $f $n as $p names $nm $[eval $gs*]?) => do
    let F ← liftCoreM <| realizeGlobalConstNoOverload f
    let N ← liftCoreM <| realizeGlobalConstNoOverload nm
    let gNames ← liftCoreM <| (gs.getD #[]).mapM fun i => realizeGlobalConstNoOverload i
    liftTermElabM do
      for g in [0:n.getNat] do
        let v ← kwhnf (mkApp (mkConst N) (mkRawNatLit g))
        let .lit (.natVal k) := v
          | throwError "#kc_rows_unfold: {N} {g} does not reduce to a literal"
        addUnfolded F gNames (p.getId.appendAfter s!"{k}") g
