module

public import Certificates.Data.Kernel.BSeed.Seed
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KC.BSeed.Gen

meta def pairT : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)

meta def chunksE (b : ByteArray) (cb salt0 : Nat) : Expr := Id.run do
  let nch := (b.size + cb - 1) / cb
  let mut acc : Expr := mkApp (mkConst ``List.nil [0]) pairT
  for k' in [0:nch] do
    let k := nch - 1 - k'
    let s := k * cb
    let e := min b.size (s + cb)
    let mut v : Nat := 0
    for i in [0:e - s] do
      v := v + ((b.get! (s + i)).toNat <<< (8 * i))
    let salt := ((salt0 + k + 1) * 11400714819323198485) % 18446744073709551616
    let p := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat)
      (mkRawNatLit ((v <<< 64) + salt)) (mkRawNatLit (e - s))
    acc := mkApp3 (mkConst ``List.cons [0]) pairT p acc
  return acc

meta def withSync (x : CoreM Unit) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) x

end CFSG.KC.BSeed.Gen

open CFSG.KC.BSeed.Gen

elab "#bs_chunk " pre:ident sId:ident rId:ident hdr:ident i0:num i1:num : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let txt ← match ((← getEnv).find? sN).bind ConstantInfo.value? with
    | some (.lit (.strVal t)) => pure t
    | _ => throwError "#bs_chunk: {sN} is not a string literal"
  let hdrE ← match hdr.getId with
    | `true => pure (mkConst ``Bool.true)
    | `false => pure (mkConst ``Bool.false)
    | h => throwError "#bs_chunk: header flag {h} is not `true` or `false`"
  let b := txt.toUTF8
  withSync do
    addDecl (forceExpose := true) <| .defnDecl
      { name := P ++ `CH, levelParams := [], type := mkApp (mkConst ``List [0]) pairT,
        value := chunksE b 256 (b.hash.toNat % 1000000007), hints := .regular 0, safety := .safe }
    withOptions (maxRecDepth.set · 400000) do
      CFSG.KC.addThmDecl <| (mkTheoremValEx (P ++ `ok) []
        (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
          (mkAppN (mkConst ``CFSG.KC.BSeed.seedChunkOK)
            #[mkRawNatLit 4370, mkApp (mkConst ``CFSG.KC.BSeed.bytesOfS) (mkConst (P ++ `CH)), hdrE,
              mkRawNatLit i0.getNat, mkRawNatLit i1.getNat, mkConst rN])
          (mkConst ``Bool.true)) reflBoolTrue [])
