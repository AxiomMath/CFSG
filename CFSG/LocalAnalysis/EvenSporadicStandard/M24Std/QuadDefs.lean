module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G]

structure SextetFactsQW (L A : Subgroup G) : Prop where
  gen45 : ∃ a₁ ∈ A, a₁ ≠ 1 ∧
    Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A
  fix : ∀ x ∈ A, x ≠ 1 → ∀ w ∈ A,
    (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x
  omega : ∃ w ∈ egNL L A, w * w * w = 1 ∧
    (∀ n ∈ egNL L A,
      (∀ a ∈ A, (n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹ = w * a * w⁻¹) ∨
      (∀ a ∈ A, (n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹ = w⁻¹ * a * w)) ∧
    ∀ a ∈ A, w * a * w⁻¹ = a → a = 1

end CFSG.EvenSporadicStandard.M24Std
