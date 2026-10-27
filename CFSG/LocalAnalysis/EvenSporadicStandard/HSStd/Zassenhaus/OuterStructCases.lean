module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Layer
public import CFSG.Assembly.Defs

public section

set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

structure OuterSwap (X : Type*) [Group X] [Finite X] (J : Subgroup X) (τ : X)
    (K : Subgroup X) : Prop where
  comp : IsComponent K
  comp' : IsComponent (PartA.cj τ K)
  ne : PartA.cj τ K ≠ K
  layer_eq : layer X = K ⊔ PartA.cj τ K
  commute : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a
  alt8 : Nonempty (↥K ≃* alternatingGroup (Fin 8))
  diag : ∀ x : X, x ∈ J ↔ ∃ k ∈ K, x = k * (τ * k * τ⁻¹)

variable {J : Subgroup X} {τ : X}

omit [Finite X] in
theorem conj_conj_of_sq {τ : X} (ht2 : τ * τ = 1) (b : X) : τ * (τ * b * τ⁻¹) * τ⁻¹ = b := by
  have hti : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right ht2
  rw [hti]
  calc τ * (τ * b * τ) * τ = (τ * τ) * b * (τ * τ) := by group
    _ = b := by rw [ht2]; group

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
