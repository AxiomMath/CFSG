module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

public section

open Lean Elab Command Meta

namespace CFSG.KC.Th.Chars

meta def literalOf (n : Name) : CoreM String := do
  let some (.defnInfo v) := (← getEnv).find? n | throwError "{n} is not a definition"
  match v.value.consumeMData with
  | .lit (.strVal s) => return s
  | e => throwError "{n} is not a string literal: {e}"

meta def addChars (L seed : Name) : CoreM Unit := do
  let s ← literalOf seed
  let charT := mkConst ``Char
  let cons := mkApp (mkConst ``List.cons [0]) charT
  let cache : Array Expr := (Array.range 128).map fun i => mkApp (mkConst ``Char.ofNat) (mkRawNatLit i)
  let mut l := mkApp (mkConst ``List.nil [0]) charT
  for ch in s.toList.reverse do
    let e := if ch.toNat < 128 then cache[ch.toNat]! else mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)
    l := mkApp2 cons e l
  let lc := mkApp (mkConst ``List [0]) charT
  addDecl (forceExpose := true) <| .defnDecl
    { name := L, levelParams := [], type := lc, value := l, hints := .regular 0, safety := .safe }
  let strT := mkConst ``String
  let ofL := mkApp (mkConst ``String.ofList) (mkConst L)
  let ty := mkApp3 (mkConst ``Eq [1]) strT (mkConst seed) ofL
  let pf1 := mkApp2 (mkConst ``Eq.refl [1]) strT (mkConst seed)
  CFSG.KC.addThmDecl <| { name := L.appendAfter "_eq", levelParams := [], type := ty, value := pf1 }
  let toL := mkConst ``String.toList
  let ty2 := mkApp3 (mkConst ``Eq [1]) lc (mkApp toL (mkConst seed)) (mkConst L)
  let cg := mkAppN (mkConst ``congrArg [1, 1])
    #[strT, lc, mkConst seed, ofL, toL, mkConst (L.appendAfter "_eq")]
  let pf := mkAppN (mkConst ``Eq.trans [1])
    #[lc, mkApp toL (mkConst seed), mkApp toL ofL, mkConst L, cg,
      mkApp (mkConst ``String.toList_ofList) (mkConst L)]
  let n2 := L.appendAfter "_toList"
  CFSG.KC.addThmDecl <| { name := n2, levelParams := [], type := ty2, value := pf }

elab "#th_chars " L:ident seed:ident : command =>
  liftCoreM <| withOptions (Elab.async.set · false) <| addChars L.getId seed.getId

meta def addCharsIn (L c : Name) : CoreM Unit := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c} is not a definition"
  let isStr : Expr → Bool := fun e => e matches .lit (.strVal _)
  let some e := d.value.find? isStr | throwError "{c}: no string literal"
  let .lit (.strVal s) := e | throwError "{c}: no string literal"
  let charT := mkConst ``Char
  let cons := mkApp (mkConst ``List.cons [0]) charT
  let mut l := mkApp (mkConst ``List.nil [0]) charT
  for ch in s.toList.reverse do
    l := mkApp2 cons (mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)) l
  let lc := mkApp (mkConst ``List [0]) charT
  addDecl (forceExpose := true) <| .defnDecl
    { name := L, levelParams := [], type := lc, value := l, hints := .regular 0, safety := .safe }
  let ofL := mkApp (mkConst ``String.ofList) (mkConst L)
  let v := d.value.replace fun e => if e matches .lit (.strVal _) then some ofL else none
  let u ← Meta.MetaM.run' (Meta.getLevel d.type)
  let ty := mkApp3 (mkConst ``Eq [u]) d.type (mkConst c) v
  let pf := mkApp2 (mkConst ``Eq.refl [u]) d.type (mkConst c)
  CFSG.KC.addThmDecl <| { name := L.appendAfter "_eq", levelParams := [], type := ty, value := pf }

elab "#th_chars_in " L:ident c:ident : command =>
  liftCoreM <| withOptions (Elab.async.set · false) <| addCharsIn L.getId c.getId

end CFSG.KC.Th.Chars
