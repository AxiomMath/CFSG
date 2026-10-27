module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup
open scoped commutatorElement

structure U34Cfg {A : Type} [Group A] (P : Subgroup A) (w : A) : Prop where
  two : IsPGroup 2 ↥P
  five : ∃ a : ℕ, w ^ (5 ^ a) = 1
  norm : w ∈ normalizer (P : Set A)
  cen : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → w * x * w⁻¹ = x
  comm_ge : 64 ≤ Nat.card ↥⁅P, zpowers w⁆
  order : ∀ x ∈ P, 8 * orderOf x < Nat.card ↥P
  big : 64 ≤ Nat.card ↥P
  center_or : 64 < Nat.card ↥P ∨
    (Nat.card ↥P = 64 ∧ 4 ≤ Nat.card ↥(center ↥P) ∧
      ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x * x = 1)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
