module

public import Mathlib.Data.Fintype.Perm

public section

namespace CFSG.EvenSporadicStandard.HSStd

@[expose] def S5ThreeProp : Prop :=
  ∀ τ μ₁ μ₂ : Equiv.Perm (Fin 5), τ * τ = 1 → τ ≠ 1 → μ₁ * μ₁ = 1 → μ₂ * μ₂ = 1 →
    (μ₁ * μ₂) ^ 3 = 1 → μ₁ * μ₂ ≠ 1 → τ * μ₁ = μ₁ * τ → τ * μ₂ = μ₂ * τ →
      ∃ i j k l : Fin 5, i ≠ j ∧ k ≠ l ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧
        τ = Equiv.swap i j ∧ (μ₁ = Equiv.swap k l ∨ μ₁ * τ = Equiv.swap k l)

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 1024 in
instance decidableS5ThreeProp : Decidable S5ThreeProp := by
  unfold S5ThreeProp
  infer_instance

end CFSG.EvenSporadicStandard.HSStd
