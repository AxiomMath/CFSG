module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Tactic

namespace CFSG.KC.HexTree

meta def digit (c : UInt8) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48).toNat
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87).toNat
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55).toNat
  else none

meta def parse (b : ByteArray) (lo hi : Nat) : Except String Nat := do
  let mut acc := 0
  for i in [lo:hi] do
    let some d := digit b[i]! | throw s!"not a hexadecimal digit at byte {i}"
    acc := acc * 16 + d
  return acc

end CFSG.KC.HexTree

elab "hex_tree " s:ident sz:num h:num d:num : tactic => liftMetaFinishingTactic fun g => do
  let n ← realizeGlobalConstNoOverloadWithInfo s
  let some (.lit (.strVal str)) := ((← getEnv).find? n).bind (·.value?)
    | throwError "hex_tree: {n} is not a string literal constant"
  let str := str.trimAscii.copy
  unless str.utf8ByteSize == sz.getNat && str.hash.toNat == h.getNat do
    throwError "hex_tree: {n} has size {str.utf8ByteSize} hash {str.hash.toNat}, pinned size \
      {sz.getNat} hash {h.getNat}"
  let d := d.getNat
  let b := str.toUTF8
  unless d > 0 && b.size % d == 0 do
    throwError "hex_tree: {n} has {b.size} digits, not a positive multiple of {d}"
  let nLeaves := b.size / d
  let mut leaves : Array Nat := #[]
  for k in [0:nLeaves] do
    match CFSG.KC.HexTree.parse b (k * d) ((k + 1) * d) with
    | .ok v => leaves := leaves.push v
    | .error e => throwError "hex_tree: {n}: {e}"
  let hgt := Nat.log2 (2 * nLeaves - 1)
  let leaf := fun k => CFSG.KC.Tab.constFn (CFSG.KC.Tab.lit (leaves.getD k 0))
  g.assign (CFSG.KC.Tab.table leaf (1 <<< hgt) 0)
