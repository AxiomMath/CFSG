module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearOuter
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearDelta

public section

namespace CFSG.SeitzReduction

namespace LinearOuter

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K] {n : ℕ}

theorem involutionCriterion_conjAut_mul_dualAut {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (hnf : ¬(n = 4 ∧ f = 1)) (A : GL (Fin n) K)
    (hα : (conjAut n K A * dualAut n K) ^ 2 = 1) :
    InvolutionCriterion (conjAut n K A * dualAut n K) := by
  by_cases hcase : Odd n ∨ ∀ v : Fin n → K, v ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0
  · exact involutionCriterion_conjAut_mul_dualAut_of_alt_or_odd hf hK (by omega)
      (fun h => hnf ⟨by omega, h.2⟩) A hα hcase
  · rw [not_or] at hcase
    exact LinearDelta.involutionCriterion_conjAut_mul_dualAut_of_even hf hK hn
      (Nat.not_odd_iff_even.mp hcase.1) hnf A hα hcase.2

theorem involutionCriterion_of_not_mem_range_conj {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) (hnf : ¬(n = 4 ∧ f = 1))
    {x : MulAut (projectiveSL n K)}
    (hxX : x ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (hx2 : x ^ 2 = 1) : InvolutionCriterion x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := n) (by omega)).2 x
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at hxX hx2 ⊢
    by_cases hσ : σ = 1
    · exfalso
      subst hσ
      rw [map_one, mul_one] at hxX hx2
      by_cases h1 : conjAut n K A = 1
      · exact hxX (h1 ▸ one_mem _)
      · obtain ⟨s, -, hs⟩ :=
          CFSG.ComponentClassification.OutcomeLocal.exists_involution_eq_conjAut (by omega) A
            hx2 h1
        exact hxX ⟨s, hs.symm⟩
    · exact involutionCriterion_conjAut_mul_fieldAut hf hK (by omega) A σ hσ hx2
  · rw [pow_one] at hxX hx2 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hx2 ⊢
      exact involutionCriterion_conjAut_mul_dualAut hf hK hn hnf A hx2
    · exact involutionCriterion_conjAut_mul_fieldAut_mul_dualAut hf hK (by omega) (by omega) A σ
        hσ hx2

end LinearOuter

end CFSG.SeitzReduction
