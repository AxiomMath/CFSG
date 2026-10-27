module

public import Certificates.Data.Kernel.YModel.Text
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

namespace CFSG.KC.BM.PktGen

meta def pairT : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)

meta def linesE (b : ByteArray) : Expr × Array Nat := Id.run do
  let mut cuts : Array (Nat × Nat) := #[]
  let mut starts : Array Nat := #[]
  let mut s := 0
  while s < b.size do
    let mut e := s
    while e < b.size && b.get! e != 10 do
      e := e + 1
    e := min b.size (e + 1)
    starts := starts.push cuts.size
    let mut q := s
    while q < e do
      cuts := cuts.push (q, min e (q + 256))
      q := q + 256
    s := e
  starts := starts.push cuts.size
  let mut acc : Expr := mkApp (mkConst ``List.nil [0]) pairT
  for k' in [0:cuts.size] do
    let (lo, hi) := cuts[cuts.size - 1 - k']!
    let mut v : Nat := 0
    for i in [0:hi - lo] do
      v := v + ((b.get! (lo + i)).toNat <<< (8 * i))
    let p := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit v)
      (mkRawNatLit (hi - lo))
    acc := mkApp3 (mkConst ``List.cons [0]) pairT p acc
  return (acc, starts)

end CFSG.KC.BM.PktGen

open CFSG.KC.BM.PktGen

elab "#text_lines " pre:ident sId:ident path:str size:num hash:num : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let b ← IO.FS.readBinFile path.getString
  unless b.size == size.getNat && b.hash.toNat == hash.getNat do
    throwError s!"{path.getString}: size {b.size} hash {b.hash.toNat}"
  let strE := mkConst ``String
  let (chE, starts) := linesE b
  let natE := mkConst ``Nat
  let sE := starts.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natE (mkRawNatLit x) acc)
    (mkApp (mkConst ``List.nil [0]) natE)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDecl (forceExpose := true) <| .defnDecl
      { name := P ++ `CH, levelParams := [], type := mkApp (mkConst ``List [0]) pairT,
        value := chE, hints := .regular 0, safety := .safe }
    addDecl (forceExpose := true) <| .defnDecl
      { name := P ++ `S, levelParams := [], type := mkApp (mkConst ``List [0]) natE,
        value := sE, hints := .regular 0, safety := .safe }
    let rhs := mkApp (mkConst ``String.ofList)
      (mkApp (mkConst ``CFSG.KC.YModel.charsOf) (mkConst (P ++ `CH)))
    let tyEq := mkApp3 (mkConst ``Eq [1]) strE (mkConst sN) rhs
    let pfEq := mkApp2 (mkConst ``Eq.refl [1]) strE (mkConst sN)
    withOptions (maxRecDepth.set · 400000) do
      CFSG.KC.addThmDecl <| (mkTheoremValEx (P ++ `eq) [] tyEq pfEq [])
