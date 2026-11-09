module

public meta import Lean

open Lean

namespace CFSG.KC.NatTree

meta def mkJoin (lo hi : Expr) (bits : Nat) : Expr :=
  mkApp2 (mkConst ``Nat.add) lo (mkApp2 (mkConst ``Nat.shiftLeft) hi (mkRawNatLit bits))

public meta partial def mkTree (leaf : Nat → Expr) (w lo hi : Nat) : Expr :=
  if hi ≤ lo + 1 then leaf lo
  else
    let mid := lo + (hi - lo) / 2
    mkJoin (mkTree leaf w lo mid) (mkTree leaf w mid hi) (w * (mid - lo))

public meta partial def natOf? (e : Expr) : CoreM (Option Nat) := do
  match e with
  | .lit (.natVal v) => return some v
  | .mdata _ e => natOf? e
  | .const n _ =>
    match (← getConstInfo n).value? (allowOpaque := true) with
    | some v => natOf? v
    | none => return none
  | _ =>
    let bin (f : Nat → Nat → Nat) : CoreM (Option Nat) := do
      let some a ← natOf? (e.getArg! 0) | return none
      let some b ← natOf? (e.getArg! 1) | return none
      return some (f a b)
    if e.isAppOfArity ``Nat.add 2 then bin (· + ·)
    else if e.isAppOfArity ``Nat.shiftLeft 2 then bin (· <<< ·)
    else return none

end CFSG.KC.NatTree
