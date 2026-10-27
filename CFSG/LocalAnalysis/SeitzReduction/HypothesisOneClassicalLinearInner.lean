module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearInnerSupply
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution

public noncomputable section

namespace CFSG.SeitzReduction.ClassicalLinear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog EvenLinearSL
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type*} [Field K] {n : ℕ}

theorem range_le_ker_of_mul_self_eq_one [CharP K 2] [NeZero n] {s : GL (Fin n) K}
    (hs : s * s = 1) :
    LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) ≤
      LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec,
    sub_one_mul_sub_one_eq_zero hs, zero_mulVec]

theorem involutionCriterion_conjAut_of_ne {f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {s : GL (Fin n) K} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hWL : LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) ≠
      LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1))) :
    InvolutionCriterion (conjAut n K s) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  obtain ⟨a₀, v₀, w₀, x₂, ha₀, hav₀, hw₀, hw₀0, hx₂L, hx₂W, hL, hW⟩ :=
    exists_rankOne_mem_closure_odd_fixed hn hs hs1 hWL
  intro β _ hβc
  have hfix : ∀ d ∈ closure {c : projectiveSL n K | conjAut n K s c = c ∧ Odd (orderOf c)},
      β d = d := fun d hd => apply_eq_self_of_mem_closure (fun c hc => hβc c hc.1 hc.2) hd
  exact sq_eq_one_of_forall_fix_rankOne (by omega) (range_le_ker_of_mul_self_eq_one hs) ha₀ hav₀
    hw₀ hw₀0 hx₂L hx₂W (fun x hx h => hfix _ (hL x hx h)) (fun m hm h => hfix _ (hW m hm h))

theorem involutionCriterion_or_lagrangian {f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {t : MulAut (projectiveSL n K)} (htI : t ∈ inner (projectiveSL n K))
    (ht : orderOf t = 2) :
    InvolutionCriterion t ∨ ∃ s : GL (Fin n) K, conjAut n K s = t ∧ s * s = 1 ∧ s ≠ 1 ∧
      LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) =
        LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨s, hst, hss, hs1⟩ := exists_involution_rep (by omega) htI ht
  by_cases hWL : LinearMap.range (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1)) =
      LinearMap.ker (mulVecLin ((s : Matrix (Fin n) (Fin n) K) - 1))
  · exact Or.inr ⟨s, hst, hss, hs1, hWL⟩
  · rw [← hst]
    exact Or.inl (involutionCriterion_conjAut_of_ne hn hf hK hss hs1 hWL)

end CFSG.SeitzReduction.ClassicalLinear
