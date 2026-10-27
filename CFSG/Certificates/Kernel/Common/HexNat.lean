module

public meta import Lean
public import Lean.Exception

open Lean Elab Tactic

namespace CFSG.KC.HexNat

meta def digit (c : UInt8) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48).toNat
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87).toNat
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55).toNat
  else none

meta partial def parse (b : ByteArray) (lo hi : Nat) : Except String Nat :=
  if hi ≤ lo + 16 then do
    let mut acc := 0
    for i in [lo:hi] do
      let some d := digit b[i]! | throw s!"not a hexadecimal digit at byte {i}"
      acc := acc * 16 + d
    return acc
  else do
    let mid := (lo + hi) / 2
    return ((← parse b lo mid) <<< (4 * (hi - mid))) + (← parse b mid hi)

end CFSG.KC.HexNat

elab "hex_nat " s:ident sz:num h:num : tactic => liftMetaFinishingTactic fun g => do
  let n ← realizeGlobalConstNoOverloadWithInfo s
  let some (.lit (.strVal str)) := ((← getEnv).find? n).bind (·.value?)
    | throwError "hex_nat: {n} is not a string literal constant"
  let str := str.trimAscii.copy
  unless str.utf8ByteSize == sz.getNat && str.hash.toNat == h.getNat do
    throwError "hex_nat: {n} has size {str.utf8ByteSize} hash {str.hash.toNat}, pinned size \
      {sz.getNat} hash {h.getNat}"
  match CFSG.KC.HexNat.parse str.toUTF8 0 str.utf8ByteSize with
  | .ok v => g.assign (mkRawNatLit v)
  | .error e => throwError "hex_nat: {n}: {e}"
