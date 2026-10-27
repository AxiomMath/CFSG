module

public import Certificates.Data.Kernel.YModel.Text
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KC.BM.B64Gen

meta def pairT : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)

meta def piecesE (b : ByteArray) (f k : Nat) : Expr := Id.run do
  let mut cuts : Array (Nat × Nat) := if f > 0 then #[(0, min f b.size)] else #[]
  let mut s := f
  while s < b.size do
    cuts := cuts.push (s, min b.size (s + k))
    s := s + k
  let mut acc : Expr := mkApp (mkConst ``List.nil [0]) pairT
  for k' in [0:cuts.size] do
    let (lo, hi) := cuts[cuts.size - 1 - k']!
    let mut v : Nat := 0
    for i in [0:hi - lo] do
      v := v + ((b.get! (lo + i)).toNat <<< (8 * i))
    let p := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit v)
      (mkRawNatLit (hi - lo))
    acc := mkApp3 (mkConst ``List.cons [0]) pairT p acc
  return acc

end CFSG.KC.BM.B64Gen

open CFSG.KC.BM.B64Gen

elab "#text_pieces " pre:ident sId:ident path:str size:num hash:num f:num k:num : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let b ← IO.FS.readBinFile path.getString
  unless b.size == size.getNat && b.hash.toNat == hash.getNat do
    throwError s!"{path.getString}: size {b.size} hash {b.hash.toNat}"
  unless k.getNat > 0 do throwError "piece size 0"
  let strE := mkConst ``String
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (forceExpose := true) <| .defnDecl
      { name := P ++ `CH, levelParams := [], type := mkApp (mkConst ``List [0]) pairT,
        value := piecesE b f.getNat k.getNat, hints := .regular 0, safety := .safe }
    let rhs := mkApp (mkConst ``String.ofList)
      (mkApp (mkConst ``CFSG.KC.YModel.charsOf) (mkConst (P ++ `CH)))
    let tyEq := mkApp3 (mkConst ``Eq [1]) strE (mkConst sN) rhs
    let pfEq := mkApp2 (mkConst ``Eq.refl [1]) strE (mkConst sN)
    withOptions (maxRecDepth.set · 400000) do
      CFSG.KC.addThmDecl <| (mkTheoremValEx (P ++ `eq) [] tyEq pfEq [])
