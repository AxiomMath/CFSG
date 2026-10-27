module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutCoprime
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP15

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_card_C (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) :
    Nat.card (ctxCY t tau x₁ x₂ rho) = 2 ^ 8 ∨ Nat.card (ctxCY t tau x₁ x₂ rho) = 2 ^ 10 := by
  have hKmem := l17_mem_K hc.toCtx13
  have hCnorm := l18_C_normal hc.toCtx13
  have hrho3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  have hρ : (MulAut.conj rho : MulAut G) ^ 3 = 1 := by
    rw [← map_pow, hrho3, map_one]
  have hH : ∀ h ∈ ctxCY t tau x₁ x₂ rho, MulAut.conj rho h ∈ ctxCY t tau x₁ x₂ rho := by
    intro h hh
    simpa only [MulAut.conj_apply] using hCnorm.2 rho hKmem.2.2.2.2 h hh
  have hfixeq : ctxCY t tau x₁ x₂ rho ⊓ Outside.fixSub (MulAut.conj rho) =
      ctxCY t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := by
    ext x
    simp only [Subgroup.mem_inf, Outside.mem_fixSub, MulAut.conj_apply,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, mul_inv_eq_iff_eq_mul.mp hx⟩
    · rintro ⟨hxC, hx⟩
      exact ⟨hxC, mul_inv_eq_iff_eq_mul.mpr hx⟩
  have hmod : Nat.card (ctxCY t tau x₁ x₂ rho) % 3 = 1 := by
    have h := Outside.card_mod_three_fix (MulAut.conj rho) hρ (ctxCY t tau x₁ x₂ rho) hH
    rw [hfixeq, l18_C_cap_cent_rho hc.toCtx13, l17_card_tauom hc.toCtx13] at h
    norm_num at h
    exact h
  have hQle : ctxQ t tau x₁ x₂ rho ≤ ctxCY t tau x₁ x₂ rho :=
    le_trans le_sup_left (l18_QA_le_C hc.toCtx13)
  have hQcard : Nat.card (ctxQ t tau x₁ x₂ rho) = 64 := IsZ4Z4E4.card hc.q_iso
  have hτC : tau ∈ ctxCY t tau x₁ x₂ rho :=
    (l18_QA_le_C hc.toCtx13) (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hτQ : tau ∉ ctxQ t tau x₁ x₂ rho := Ctx13.tau_not_mem_Q hc.toCtx13
  have hCne : Nat.card (ctxCY t tau x₁ x₂ rho) ≠ 64 := by
    intro h64
    have hQC : ctxQ t tau x₁ x₂ rho = ctxCY t tau x₁ x₂ rho :=
      Subgroup.eq_of_le_of_card_ge hQle (by rw [h64, hQcard])
    exact hτQ (hQC.symm ▸ hτC)
  have hdivS : Nat.card (ctxCY t tau x₁ x₂ rho) ∣ 2 ^ 12 := by
    have h := Subgroup.card_dvd_of_le (l18_C_le_sylow hc.toCtx18S)
    rwa [l18_card_sylow hc.toCtx18S] at h
  obtain ⟨j, hj_le, hjC⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdivS
  have h6dvd : 2 ^ 6 ∣ 2 ^ j := by
    have hdvd : Nat.card (ctxQ t tau x₁ x₂ rho) ∣ Nat.card (ctxCY t tau x₁ x₂ rho) :=
      Subgroup.card_dvd_of_le hQle
    rw [hjC, hQcard] at hdvd
    have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rwa [h64] at hdvd
  have h6le : 6 ≤ j := by
    have hle : 2 ^ 6 ≤ 2 ^ j := Nat.le_of_dvd (by positivity) h6dvd
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1:ℕ) < 2)).mp hle
  have hj_ne6 : j ≠ 6 := by
    intro h
    exact hCne (by rw [hjC, h]; norm_num)
  have hj_ge : 7 ≤ j := by omega
  have hB : closure ({t, lam} : Set G) ≤ 𝒮 := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact (l18_T_le_sylow hc.toCtx18S).1
    · exact (l18_T_le_sylow hc.toCtx18S).2.2.2
  have hmul := card_mul_le_of_inf_eq_bot (l18_C_le_sylow hc.toCtx18S) hB
    (l18_C_inf_tlam hc.toCtx13)
  rw [l18_card_sylow hc.toCtx18S, l17_card_tlam hc.toCtx13] at hmul
  have hj_le10 : j ≤ 10 := by
    have h2 : 2 ^ (j + 2) ≤ 2 ^ 12 := by
      calc 2 ^ (j + 2) = 2 ^ j * 4 := by rw [pow_add]; norm_num
        _ = Nat.card (ctxCY t tau x₁ x₂ rho) * 4 := by rw [hjC]
        _ ≤ 2 ^ 12 := hmul
    have := (Nat.pow_le_pow_iff_right (by norm_num : (1:ℕ) < 2)).mp h2
    omega
  have hmodj : 2 ^ j % 3 = 1 := by rw [← hjC]; exact hmod
  have hj_cases : j = 8 ∨ j = 10 := by
    interval_cases j
    · norm_num at hmodj
    · exact Or.inl rfl
    · norm_num at hmodj
    · exact Or.inr rfl
  rcases hj_cases with rfl | rfl
  · left; rw [hjC]
  · right; rw [hjC]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
