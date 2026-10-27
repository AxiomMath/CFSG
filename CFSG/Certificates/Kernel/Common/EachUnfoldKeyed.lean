module

public meta import Lean
public import CFSG.Certificates.Kernel.Common.EachUnfold
meta import all CFSG.Certificates.Kernel.Common.EachUnfold

open Lean Elab Command Meta

namespace CFSG.KC.EachUnfoldKeyed

open CFSG.KC.EachUnfold

meta def run (f p k : Ident) (lo hi : Nat) (s : Option String) (gs : Array Ident) :
    CommandElabM Unit := do
  let F ← liftCoreM <| realizeGlobalConstNoOverload f
  let K ← liftCoreM <| realizeGlobalConstNoOverload k
  let gNames ← liftCoreM <| gs.mapM fun i => realizeGlobalConstNoOverload i
  liftTermElabM do
    let mut seen : Std.HashMap Nat Nat := {}
    for i in [lo:hi] do
      let some kv := natVal? (← literal (mkApp (mkConst K) (mkRawNatLit i)))
        | throwError "#kc_each_unfold_keyed: {K} {i} is not a number"
      let j := seen.getD kv 0
      seen := seen.insert kv (j + 1)
      addUnfolded F gNames (p.getId.appendAfter s!"{kv}_{s.getD s!"{j}"}") i

end CFSG.KC.EachUnfoldKeyed

elab "#kc_each_unfold_keyed " f:ident lo:num hi:num " as " p:ident &" key " k:ident
    " eval" gs:ident* : command =>
  CFSG.KC.EachUnfoldKeyed.run f p k lo.getNat hi.getNat none gs

elab "#kc_each_unfold_keyed " f:ident lo:num hi:num " as " p:ident &" key " k:ident
    &" sfx " s:ident " eval" gs:ident* : command =>
  CFSG.KC.EachUnfoldKeyed.run f p k lo.getNat hi.getNat (some s.getId.toString) gs
