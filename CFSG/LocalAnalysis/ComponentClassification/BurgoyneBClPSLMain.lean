module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClPSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClGraph
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClField

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem noL2At_psl {n : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hKc : Nat.card K = p ^ f) (hn : 6 ≤ n)
    {v : MulAut (projectiveSL n K)} (hv : orderOf v = 2) : NoL2At v := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hsq : v ^ 2 = 1 := by rw [← hv, pow_orderOf_eq_one]
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) (by omega : 3 ≤ n)).2 v
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα
      subst hα
      exact noL2At_conjAut hK hn hv
    · subst hα
      exact noL2At_field hp hp2 hf hKc (by omega) hσ hsq
  · rw [pow_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      have hsq' : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1 := by
        rw [← hα]
        exact hsq
      rw [map_one, mul_one] at hα
      subst hα
      rcases LocalAnalysis.ComponentInitial.OddHigherLinear.transpose_eq_or_eq_neg_of_sq
          (by omega) A hsq' with hA | hA
      · exact noL2At_conj_dual_sym hK hn hA
      · exact noL2At_conj_dual_alt hK (by omega) hA
    · subst hα
      exact noL2At_graphField hp hp2 hf hKc (by omega) hσ hsq

theorem noL2At_of_lieModel_PSL {S : Type} [Group S] [Finite S] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : 6 ≤ n) (hL : CFSG.Blueprint.LieModel S .PSL n p f) {v : MulAut S}
    (hv : orderOf v = 2) : NoL2At v := by
  obtain ⟨hp, hf⟩ : p.Prime ∧ 1 ≤ f := by
    rcases hL with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact ⟨h.1, h.2.1⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, hKc, ⟨θ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  refine NoL2At.of_congr θ (noL2At_psl hp hp2 hf hKc hn ?_)
  rw [MulEquiv.orderOf_eq]
  exact hv

end CFSG.ComponentClassification.Burgoyne.Cl
