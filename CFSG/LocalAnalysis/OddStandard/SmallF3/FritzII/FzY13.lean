module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_eight_of_ctx0 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨-, hfel, hf4⟩ := h.wreath.fourGrp_eq_omega
  have hF_le : fourGrp x₁ x₂ ≤ L := by
    have hT : wreathGrp x₁ x₂ lam ≤ L := h.inf_eq ▸ inf_le_right
    have hx₁ : x₁ ∈ wreathGrp x₁ x₂ lam := subset_closure (by simp)
    have hx₂ : x₂ ∈ wreathGrp x₁ x₂ lam := subset_closure (by simp)
    rw [fourGrp, closure_le]
    rintro g (rfl | rfl)
    · exact hT (pow_mem hx₁ 2)
    · exact hT (pow_mem (mul_mem hx₁ hx₂) 2)
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp h.hyp.ord_t).1
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ fourGrp x₁ x₂, a * b = b * a := by
    intro a ha b hb
    have hcent : t ∈ Subgroup.centralizer (L : Set G) := h.hyp.mem_centralizer
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    have hk : t ^ k ∈ Subgroup.centralizer (L : Set G) := zpow_mem hcent k
    exact ((Subgroup.mem_centralizer_iff.mp hk) b (hF_le hb)).symm
  have hinf : zpowers t ⊓ fourGrp x₁ x₂ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg1
    have hk : t ^ k = 1 ∨ t ^ k = t := by
      have hmod : t ^ (k % 2) = t ^ k := by
        have := zpow_mod_orderOf t k
        rw [h.hyp.ord_t] at this
        simpa using this
      rw [← hmod]
      have h02 : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases h02 with h0 | h0 <;> simp [h0]
    rcases hk with hk | hk
    · exact (mem_bot.mpr hk)
    · exfalso
      have htL : t ∈ L := by rw [← hk]; exact hF_le hg2
      have htP : t ∈ twoCore t ⊓ L := ⟨h.hyp.mem_twoCore, htL⟩
      rw [h.hyp.twoCore_inf, mem_bot] at htP
      have := h.hyp.ord_t
      rw [htP, orderOf_one] at this
      exact absurd this (by norm_num)
  refine ⟨zpowers t ⊔ fourGrp x₁ x₂, ⟨?_, ?_⟩, ?_⟩
  · exact isMulCommutative_sup_of_commute hcomm inferInstance hfel.1
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcomm).1 hx
    have ha2 : a ^ 2 = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
    have hb2 : b ^ 2 = 1 := hfel.2 b hb
    have hc : Commute a b := hcomm a ha b hb
    rw [hc.mul_pow, ha2, hb2, mul_one]
  · rw [card_sup_of_commute hcomm hinf, Nat.card_zpowers, h.hyp.ord_t, hf4]

theorem three_le_twoRank_of_ctx0 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : Ctx0 t L S x₁ x₂ lam rho) : 3 ≤ CFSG.Open.twoRank G := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_eight_of_ctx0 h
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, le_top, hE, by rw [hcard]; norm_num⟩
  rintro k ⟨E', -, -, hE'⟩
  calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    _ = Nat.card E' := hE'.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group E'

theorem not_four_generated_of_ctx0
    (hGH : CFSG.ComponentClassification.UFrontier.GH74ModelsInput) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hnc : ¬ Blueprint.Catalog G) {t : G}
    {L S : Subgroup G} {x₁ x₂ lam rho : G} (h : Ctx0 t L S x₁ x₂ lam rho) :
    ¬ ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P := fun hsect =>
  hnc (CFSG.ComponentClassification.UFrontier.catalog_of_gh74 hGH hnonab
    (three_le_twoRank_of_ctx0 h) hsect)

end CFSG.OddStandard.SmallF3.FritzII
