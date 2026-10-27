module

public import Certificates.Data.Kernel.YModel.Text
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

namespace CFSG.KC.YModel.GenS

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE

meta def mkNatList (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) natE e acc) (mkApp (mkConst ``List.nil [0]) natE)

meta def addDef (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta def pairT : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat)

meta def chunksE (b : ByteArray) (cb : Nat) : Expr := Id.run do
  let nch := (b.size + cb - 1) / cb
  let mut acc : Expr := mkApp (mkConst ``List.nil [0]) pairT
  for k' in [0:nch] do
    let k := nch - 1 - k'
    let s := k * cb
    let e := min b.size (s + cb)
    let mut v : Nat := 0
    for i in [0:e - s] do
      v := v + ((b.get! (s + i)).toNat <<< (8 * i))
    let p := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkRawNatLit v)
      (mkRawNatLit (e - s))
    acc := mkApp3 (mkConst ``List.cons [0]) pairT p acc
  return acc

meta def packLines (s : String) (w sgn : Nat) : Array Nat × Array Nat := Id.run do
  let ls := ((s.splitOn "\n").filter (· ≠ "")).toArray
  let mut F : Array Nat := #[]
  let mut E : Array Nat := #[]
  for L in [0:ls.size] do
    let toks := (ls[L]!).splitOn " "
    let mut acc := 0
    let mut e := 0
    for t in toks do
      let neg := t.startsWith "-"
      let v := (if neg then t.drop 1 else t).toString.toNat!
      let x := if L < sgn then v else 2 * v + (if neg then 1 else 0)
      acc := acc ||| (x <<< (w * e))
      e := e + 1
    F := F.push acc
    E := E.push e
  return (F, E)

elab "#ym_texts " pre:ident sId:ident wN:num sgnN:num : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s0 ← liftTermElabM <| unsafe evalConst String sN
  let d := (s0.toList.takeWhile (· == '\n')).length
  let s := String.ofList (s0.toList.drop d)
  let b := s.toUTF8
  let w := wN.getNat
  let (F, E) := packLines s w (if sgnN.getNat == 0 then 1000000000 else sgnN.getNat)
  let sgn := if sgnN.getNat == 0 then F.size else sgnN.getNat
  let strE := mkConst ``String
  let chunksOf (x n : Nat) : Array Nat := Id.run do
    let mut out : Array Nat := #[]
    let mut y := x
    for _ in [0:(n + 31) / 32] do
      out := out.push (y % (2 ^ (32 * w)))
      y := y / (2 ^ (32 * w))
    return out
  let listListE : Expr := mkApp (mkConst ``List [0]) listNatE
  let clE : Expr := (F.zip E).foldr (fun (x, n) acc => mkApp3 (mkConst ``List.cons [0]) listNatE
    (mkNatList ((chunksOf x n).map mkRawNatLit)) acc) (mkApp (mkConst ``List.nil [0]) listNatE)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `CH) (mkApp (mkConst ``List [0]) pairT) (chunksE b 256)
    addDef (P ++ `Cl) listListE clE
    addDef (P ++ `El) listNatE (mkNatList (E.map mkRawNatLit))
    addDef (P ++ `F) (mkForall `L .default natE natE) (mkLambda `L .default natE
      (mkApp2 (mkConst ``CFSG.KC.YModel.joinW) (mkRawNatLit w)
        (mkApp2 (mkConst ``CFSG.KC.YModel.lgetL) (mkConst (P ++ `Cl)) (mkBVar 0))))
    addDef (P ++ `lines) natE (mkRawNatLit F.size)
    let charE := mkConst ``Char
    let pre := mkApp3 (mkConst ``List.replicate [0]) charE (mkRawNatLit d)
      (mkApp (mkConst ``Char.ofNat) (mkRawNatLit 10))
    let rhs := mkApp (mkConst ``String.ofList) (mkApp3 (mkConst ``List.append [0]) charE pre
      (mkApp (mkConst ``CFSG.KC.YModel.charsOf) (mkConst (P ++ `CH))))
    let tyEq := mkApp3 (mkConst ``Eq [1]) strE (mkConst sN) rhs
    let pfEq := mkApp2 (mkConst ``Eq.refl [1]) strE (mkConst sN)
    withOptions (maxRecDepth.set · 400000) do
      CFSG.KC.addThmDecl <| (mkTheoremValEx (P ++ `eq) [] tyEq pfEq [])
      let b := mkAppN (mkConst ``CFSG.KC.YModel.decBind)
        #[mkApp (mkConst ``CFSG.KC.YModel.bytesOf) (mkConst (P ++ `CH)), mkRawNatLit w,
          mkConst (P ++ `lines), mkRawNatLit sgn,
          mkApp (mkConst ``CFSG.KC.YModel.lgetL) (mkConst (P ++ `Cl)),
          mkApp (mkConst ``CFSG.KC.YModel.lget) (mkConst (P ++ `El))]
      CFSG.KC.addThmDecl <| (mkTheoremValEx (P ++ `ok) []
        (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)) reflBoolTrue [])

end CFSG.KC.YModel.GenS
