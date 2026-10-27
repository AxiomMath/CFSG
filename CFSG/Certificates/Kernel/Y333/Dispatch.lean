module

public meta import Lean

open Lean Elab Command

namespace CFSG.KC.Dispatch

meta def natE : Expr := mkConst ``Nat

meta def fnT : Expr := mkForall `b .default natE natE

meta def addExposed (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

meta partial def bitTree (leafs : Array Expr) (p k off : Nat) : Expr :=
  if k == 0 then leafs[off]!
  else
    let bit := mkApp2 (mkConst ``Nat.beq)
      (mkApp2 (mkConst ``Nat.land) (.bvar 0) (mkRawNatLit (1 <<< (p - 1)))) (mkRawNatLit 0)
    let lo := bitTree leafs (p - 1) (k - 1) off
    let hi := bitTree leafs (p - 1) (k - 1) (off + (1 <<< (k - 1)))
    mkApp4 (mkConst ``Bool.rec [1]) (mkLambda `x .default (mkConst ``Bool) natE) hi lo bit

meta partial def addNodes (leaf : Nat → Expr) (name : Name) (lo h fan : Nat) : CoreM Unit := do
  let k := min fan h
  let children ← if k == h then
      pure <| (Array.range (1 <<< k)).map fun c => leaf (lo + c)
    else
      (Array.range (1 <<< k)).mapM fun c => do
        let cn := name ++ Name.mkSimple s!"c{c}"
        addNodes leaf cn (lo + (c <<< (h - k))) (h - k) fan
        pure (mkApp (mkConst cn) (.bvar 0))
  addExposed name fnT (mkLambda `b .default natE (bitTree children h k 0))

end CFSG.KC.Dispatch

open CFSG.KC.Dispatch in
elab "#kc_natDispatch " f:ident w:ident n:num fan:num : command => do
  let n := n.getNat
  let h := Nat.log2 (2 * n - 1)
  let F := f.getId
  let W := w.getId
  let leaf := fun k => if k < n then mkConst (W.appendAfter s!"{k}") else mkRawNatLit 0
  liftCoreM <| withOptions (Elab.async.set · false) do
    addNodes leaf (F ++ `tree) 0 h fan.getNat
    let body := mkApp4 (mkConst ``Bool.rec [1]) (mkLambda `x .default (mkConst ``Bool) natE)
      (mkRawNatLit 0) (mkApp (mkConst (F ++ `tree)) (.bvar 0))
      (mkApp2 (mkConst ``Nat.blt) (.bvar 0) (mkRawNatLit n))
    addExposed F fnT (mkLambda `b .default natE body)
