module

public meta import Lean
public import Certificates.Data.Kernel.KeyTree
public import Lean.Exception

open Lean Elab Command Meta

namespace CFSG.KC.KeyTreeLit

meta partial def natsOf (e : Expr) (acc : Array Nat) : MetaM (Array Nat) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then return acc
  if e.isAppOfArity ``List.cons 3 then
    let h := (e.getArg! 1).consumeMData
    let acc ← match h with
      | .lit (.natVal n) => pure (acc.push n)
      | _ =>
        if h.isAppOfArity ``OfNat.ofNat 3 then
          match (h.getArg! 1).consumeMData with
          | .lit (.natVal n) => pure (acc.push n)
          | _ => throwError "#kc_keytree: not a literal: {h}"
        else natsOf h acc
    return ← natsOf (e.getArg! 2) acc
  throwError "#kc_keytree: not a list literal: {e}"

meta partial def build (ks : Array Nat) (lo n : Nat) : Expr :=
  if n == 0 then mkConst ``CFSG.KC.KeyTree.KT.leaf else
    let m := (n - 1) / 2
    mkApp4 (mkConst ``CFSG.KC.KeyTree.KT.node) (build ks lo m) (mkRawNatLit ks[lo + m]!)
      (mkRawNatLit (lo + m)) (build ks (lo + m + 1) (n - 1 - m))

end CFSG.KC.KeyTreeLit

open CFSG.KC.KeyTreeLit in
elab "#kc_keytree " t:ident l:ident : command => do
  let src ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
  let some (.defnInfo d) := (← getEnv).find? src
    | throwError "#kc_keytree: {src} is not a definition with a visible value"
  let ks ← liftTermElabM <| natsOf d.value #[]
  let v := build ks 0 ks.size
  liftCoreM <| withOptions (Elab.async.set · false) <|
    addDecl (forceExpose := true) <| .defnDecl
      { name := t.getId, levelParams := [], type := mkConst ``CFSG.KC.KeyTree.KT, value := v,
        hints := .regular 0, safety := .safe }
