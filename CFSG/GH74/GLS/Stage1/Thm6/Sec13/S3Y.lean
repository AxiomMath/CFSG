module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Norm

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def YFacts (V P : Subgroup G) : Prop :=
  (∃ D : Subgroup G, DData V P D) ∧
  (∀ w ∈ P, w * w = 1 → w ∉ V → ∀ z ∈ V, ∃ h ∈ P, ⁅w, h⁆ = z) ∧
  (∀ u ∈ P, u * u = 1 → ∃ A : Subgroup G, A ≤ P ∧ u ∈ A ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ 16 ≤ Nat.card A) ∧
  (∃ a ∈ P, a * a ≠ 1) ∧
  (∃ m : ℕ, 2 ≤ m ∧ Nat.card P = 4 ^ m)

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
