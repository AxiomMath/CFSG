module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {K : Type*} [Group K] {B : Subgroup K}

theorem fixes_le_one_of_stronglyEmbedded (hB : fusionStronglyEmbedded B) {c : K}
    (hc : orderOf c = 2) {α β : K ⧸ B} (hα : c • α = α) (hβ : c • β = β) : α = β := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective α
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective β
  rw [smul_mk_eq_mk_iff] at hα hβ
  by_contra hne
  have hg : b⁻¹ * a ∉ B := by
    intro h
    apply hne
    rw [QuotientGroup.eq]
    simpa only [mul_inv_rev, inv_inv] using B.inv_mem h
  have hodd := hB.2.2 (b⁻¹ * a) hg
  have hmem : a⁻¹ * c * a ∈ B ⊓ B.map (MulAut.conj (b⁻¹ * a)⁻¹).toMonoidHom := by
    refine ⟨hα, b⁻¹ * c * b, hβ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
    group
  have horder : orderOf (⟨a⁻¹ * c * a, hmem⟩ :
      ↥(B ⊓ B.map (MulAut.conj (b⁻¹ * a)⁻¹).toMonoidHom)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (a⁻¹ * c * a) = 2
    simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj a⁻¹).orderOf_eq c).trans hc
  exact hodd.not_two_dvd_nat (horder ▸ orderOf_dvd_natCard _)

variable [Finite K]

theorem exists_fixed_of_stronglyEmbedded (hB : fusionStronglyEmbedded B) {i : K}
    (hi : orderOf i = 2) : ∃ α : K ⧸ B, i • α = α := by
  have hii : i * i = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hi).1
  have hodd : Odd (Nat.card (K ⧸ B)) := stronglyEmbedded_index_odd hB
  exact exists_fixed_of_involutive_odd_card (fun α => i • α)
    (fun α => by rw [← mul_smul, hii, one_smul]) hodd

theorem isConj_of_stronglyEmbedded (hB : fusionStronglyEmbedded B) {i j : K}
    (hi : orderOf i = 2) (hj : orderOf j = 2) : IsConj i j := by
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := B) 2 (even_iff_two_dvd.mp hB.2.1)
  have hkK : orderOf (k : K) = 2 := (Subgroup.orderOf_coe k).trans hk
  suffices h : ∀ i : K, orderOf i = 2 → IsConj (k : K) i from
    (h i hi).symm.trans (h j hj)
  intro i hi
  have hkk : (k : K) * k = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hkK).1
  have hii : i * i = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hi).1
  obtain ⟨α, hα⟩ := exists_fixed_of_stronglyEmbedded hB hi
  have hkbase : (k : K) • (QuotientGroup.mk 1 : K ⧸ B) = QuotientGroup.mk 1 :=
    class_mem_iff_fixes_base.mp k.property
  obtain ⟨g, hg⟩ : ∃ g : K, g⁻¹ • (QuotientGroup.mk 1 : K ⧸ B) ≠ α := by
    obtain ⟨b, hb⟩ : ∃ b : K, b ∉ B := by
      by_contra h
      exact hB.1 (eq_top_iff.mpr fun g _ => not_not.mp (not_exists.mp h g))
    by_cases h1 : α = QuotientGroup.mk 1
    · refine ⟨b⁻¹, ?_⟩
      rw [inv_inv, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, h1]
      exact fun h => hb ((mk_eq_base_iff b).mp h)
    · exact ⟨1, by rw [inv_one, one_smul]; exact fun h => h1 h.symm⟩
  let r := g⁻¹ * (k : K) * g
  have hr : orderOf r = 2 := by
    simpa only [r, MulAut.conj_apply, inv_inv] using
      ((MulAut.conj g⁻¹).orderOf_eq (k : K)).trans hkK
  have hrr : r * r = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hr).1
  have hrfix : r • (g⁻¹ • (QuotientGroup.mk 1 : K ⧸ B)) = g⁻¹ • QuotientGroup.mk 1 := by
    rw [conj_smul_eq_iff, smul_inv_smul, hkbase]
  have hodd : Odd (orderOf (i * r)) := by
    by_contra heven
    obtain ⟨c, hc, -, hic, hrc⟩ := central_rotation_of_even_involution_product hi hr
      (Nat.not_odd_iff_even.mp heven)
    have hcα : c • α = α := by
      apply fixes_le_one_of_stronglyEmbedded hB hi (β := α) _ hα
      rw [← mul_smul, hic.eq, mul_smul, hα]
    have hcβ : c • (g⁻¹ • (QuotientGroup.mk 1 : K ⧸ B)) = g⁻¹ • QuotientGroup.mk 1 := by
      apply fixes_le_one_of_stronglyEmbedded hB hr _ hrfix
      rw [← mul_smul, hrc.eq, mul_smul, hrfix]
    exact hg (fixes_le_one_of_stronglyEmbedded hB hc hcβ hcα)
  obtain ⟨h, hh⟩ := conj_of_odd_mul hii hrr hodd
  have hri : IsConj i r := isConj_iff.mpr ⟨h⁻¹, by rw [hh]; group⟩
  have hkr : IsConj (k : K) r := isConj_iff.mpr ⟨g⁻¹, by simp only [r, inv_inv]⟩
  exact hkr.trans hri.symm

end CFSG.ComponentClassification.AschbacherStrongEmbedding
