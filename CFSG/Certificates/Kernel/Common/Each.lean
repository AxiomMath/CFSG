module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

elab "#kc_each " f:ident lo:num hi:num : command => do
  let F ← liftCoreM <| realizeGlobalConstNoOverload f
  let boolE := mkConst ``Bool
  liftCoreM <| withOptions (Elab.async.set · false) do
    for k in [lo.getNat:hi.getNat] do
      let ty := mkApp3 (mkConst ``Eq [1]) boolE (mkApp (mkConst F) (mkRawNatLit k))
        (mkConst ``Bool.true)
      CFSG.KC.addThmDecl <|
        { name := F.appendAfter s!"{k}", levelParams := [], type := ty, value := reflBoolTrue }
