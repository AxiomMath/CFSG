module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q15F

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q15_normal_Q1 (h : L41GPh10 t L S x₁ x₂ lam rho) :
    NormalIn (l41Q1 t x₁ x₂ rho) (l41M t x₁ x₂ rho) := by
  have hQN : l41Q t x₁ x₂ rho ≤ normalizer ((l41Q1 t x₁ x₂ rho : Subgroup G) : Set G) :=
    fun a ha => mem_normalizer_of_conj_mem fun x hx => by
      unfold l41Q1 at hx ⊢
      exact q15_conj_commutator_left ha hx
  have hρN : rho ∈ normalizer ((l41Q1 t x₁ x₂ rho : Subgroup G) : Set G) :=
    q15_mem_normalizer_commutator (q14_mem_normalizer_Q (q14_rho_mem_M h.toL41GPh8))
      (Subgroup.le_normalizer (Subgroup.mem_zpowers rho))
  have hlamN : lam ∈ normalizer ((l41Q1 t x₁ x₂ rho : Subgroup G) : Set G) :=
    q15_mem_normalizer_commutator (q14_mem_normalizer_Q (q14_lam_mem_M h.toL41GPh8))
      (q15_mem_normalizer_zpowers (Or.inl h.toCtx0.lam_rho))
  have hMN : l41M t x₁ x₂ rho ≤ normalizer ((l41Q1 t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [q14_M_eq h]
    refine sup_le hQN ?_
    rw [Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hρN
    · exact hlamN
  unfold NormalIn
  refine ⟨(q15_Q1_le_Q h.toL41GPh8).trans (q14_Q_le_M t x₁ x₂ rho), fun g hg k hk => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hMN hg) k).mp hk

theorem q15_V1_eq (hQ : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t) :
    l41V1 t x₁ x₂ rho lam = l41Q t x₁ x₂ rho ⊔ zpowers lam := by
  have hcl : closure ({t, lam} : Set G) = zpowers t ⊔ zpowers lam := by
    rw [Set.insert_eq t ({lam} : Set G), Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure t, ← Subgroup.zpowers_eq_closure lam]
  calc l41V1 t x₁ x₂ rho lam = l41Q1 t x₁ x₂ rho ⊔ (zpowers t ⊔ zpowers lam) := by
        rw [l41V1, hcl]
    _ = (l41Q1 t x₁ x₂ rho ⊔ zpowers t) ⊔ zpowers lam := (sup_assoc _ _ _).symm
    _ = l41Q t x₁ x₂ rho ⊔ zpowers lam := by rw [← hQ]

theorem q15_V1_le_M (h : L41GPh10 t L S x₁ x₂ lam rho)
    (hQ : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t) :
    l41V1 t x₁ x₂ rho lam ≤ l41M t x₁ x₂ rho := by
  rw [q15_V1_eq hQ]
  exact sup_le (q14_Q_le_M t x₁ x₂ rho)
    (Subgroup.zpowers_le.mpr (q14_lam_mem_M h.toL41GPh8))

theorem q15_V1_pGroup (h : L41GPh10 t L S x₁ x₂ lam rho)
    (hQ : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t) :
    IsPGroup 2 (l41V1 t x₁ x₂ rho lam) := by
  rw [q15_V1_eq hQ]
  refine IsPGroup.to_sup_of_normal_left' (q14_Q_isPGroup t x₁ x₂ rho) ?_ ?_
  · exact IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, h.toCtx0.wreath.ord_lam]; norm_num)
  · exact Subgroup.zpowers_le.mpr (q14_mem_normalizer_Q (q14_lam_mem_M h.toL41GPh8))

theorem q15_card_V1 (h : L41GPh10 t L S x₁ x₂ lam rho)
    (hQ : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t) :
    Nat.card (l41V1 t x₁ x₂ rho lam) = 2 ^ 10 := by
  have hzple : zpowers lam ≤ closure ({rho, lam} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have h1 : l41Q t x₁ x₂ rho ⊓ zpowers lam ≤
      l41Q t x₁ x₂ rho ⊓ closure ({rho, lam} : Set G) :=
    le_inf inf_le_left (inf_le_right.trans hzple)
  have hinf : l41Q t x₁ x₂ rho ⊓ zpowers lam = ⊥ :=
    le_bot_iff.mp (h1.trans (q14_inf_K_Q h).le)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (q15_V1_pGroup h hQ)
  have hge : 2 ^ 10 ≤ 2 ^ k := by
    rw [← hk, q15_V1_eq hQ]
    have hmul := m11_card_mul_le_sup hinf
    rw [q14_card_Q h, Nat.card_zpowers, h.toCtx0.wreath.ord_lam] at hmul
    norm_num at hmul ⊢
    exact hmul
  have hdvd : 2 ^ k ∣ 3072 := by
    have h1 : Nat.card (l41V1 t x₁ x₂ rho lam) ∣ Nat.card (l41M t x₁ x₂ rho) :=
      Subgroup.card_dvd_of_le (q15_V1_le_M h hQ)
    rw [q14_card_M h, hk] at h1
    exact h1
  have hk_cases : k = 10 := by
    have hk_ge : 10 ≤ k := by
      by_contra hlt
      rw [not_le] at hlt
      have hle : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcontra : 2 ^ 10 ≤ 2 ^ 9 := hge.trans hle
      norm_num at hcontra
    have hk_le : k ≤ 11 := by
      by_contra hlt
      rw [not_le] at hlt
      have hdiv : 2 ^ 12 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have hcontra : 2 ^ 12 ∣ 3072 := hdiv.trans hdvd
      norm_num at hcontra
    have hne : k ≠ 11 := by
      rintro rfl
      norm_num at hdvd
    omega
  rw [hk, hk_cases]

theorem q15_V1_sylow (h : L41GPh10 t L S x₁ x₂ lam rho)
    (hQ : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t) :
    ¬ 2 ∣ (l41V1 t x₁ x₂ rho lam).relIndex (l41M t x₁ x₂ rho) := by
  have hle := q15_V1_le_M h hQ
  have hrel := Subgroup.relIndex_mul_card (H := l41V1 t x₁ x₂ rho lam)
    (K := l41M t x₁ x₂ rho)
  rw [inf_eq_left.mpr hle, q15_card_V1 h hQ, q14_card_M h] at hrel
  have h3 : (l41V1 t x₁ x₂ rho lam).relIndex (l41M t x₁ x₂ rho) = 3 := by
    norm_num at hrel
    omega
  rw [h3]
  norm_num

theorem q15_V1_not_sylow (h : L41Ph10 t L S x₁ x₂ lam rho)
    (hQ : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t) :
    2 ∣ (l41V1 t x₁ x₂ rho lam).index := by
  have hcard := Subgroup.card_mul_index (H := l41V1 t x₁ x₂ rho lam)
  rw [q15_card_V1 h.toG hQ] at hcard
  have hdvd : 2 ^ 10 * 2 ∣ 2 ^ 10 * (l41V1 t x₁ x₂ rho lam).index := by
    rw [hcard]
    rw [show (2 : ℕ) ^ 10 * 2 = 2 ^ 11 by norm_num]
    exact h.glob.dvd
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 2 ^ 10) hdvd

end Q15F

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
