module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Labelled
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_conj_rep {G : Type} [Group G] {a : G} {z₀ b u : ↥(Gx a)}
    (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u) {t : G} (ht : t ∈ Gx a) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) :
    t = a ∨ (∃ k ∈ Gx a, k * (z₀ : G) * k⁻¹ = t) ∨ (∃ k ∈ Gx a, k * (a * z₀ : G) * k⁻¹ = t) ∨
      (∃ k ∈ Gx a, k * (b : G) * k⁻¹ = t) ∨ (∃ k ∈ Gx a, k * (u : G) * k⁻¹ = t) := by
  have ht'2 : (⟨t, ht⟩ : ↥(Gx a)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using ht2
  have ht'1 : (⟨t, ht⟩ : ↥(Gx a)) ≠ 1 := by
    intro h
    exact ht1 (by simpa using congrArg Subtype.val h)
  have ht'ord : orderOf (⟨t, ht⟩ : ↥(Gx a)) = 2 := orderOf_eq_prime ht'2 ht'1
  obtain ⟨i, hi⟩ := hF.involution_cover ⟨t, ht⟩ ht'ord
  fin_cases i
  ·
    change IsConj (GxSelf a) (⟨t, ht⟩ : ↥(Gx a)) at hi
    left
    have hself_center : GxSelf a ∈ Subgroup.center ↥(Gx a) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp g.2
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    have hfix : c * GxSelf a * c⁻¹ = GxSelf a := by
      rw [Subgroup.mem_center_iff.mp hself_center c, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix] at hc
    exact congrArg Subtype.val hc.symm
  ·
    change IsConj z₀ (⟨t, ht⟩ : ↥(Gx a)) at hi
    right; left
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    exact ⟨(c : G), c.2, by
      have h := congrArg Subtype.val hc
      simpa using h⟩
  ·
    change IsConj (GxSelf a * z₀) (⟨t, ht⟩ : ↥(Gx a)) at hi
    right; right; left
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    exact ⟨(c : G), c.2, by
      have h := congrArg Subtype.val hc
      simpa [GxSelf] using h⟩
  ·
    change IsConj b (⟨t, ht⟩ : ↥(Gx a)) at hi
    right; right; right; left
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    exact ⟨(c : G), c.2, by
      have h := congrArg Subtype.val hc
      simpa using h⟩
  ·
    change IsConj u (⟨t, ht⟩ : ↥(Gx a)) at hi
    right; right; right; right
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    exact ⟨(c : G), c.2, by
      have h := congrArg Subtype.val hc
      simpa using h⟩

theorem mem_derivedOf_of_conj_inner {G : Type} [Group G] {a : G} {z₀ b u : ↥(Gx a)}
    (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u) {t : G}
    (ht : (∃ k ∈ Gx a, k * (z₀ : G) * k⁻¹ = t) ∨ (∃ k ∈ Gx a, k * (a * z₀ : G) * k⁻¹ = t)) :
    t ∈ derivedOf (Gx a) := by
  have hz₀ : (z₀ : G) ∈ derivedOf (Gx a) := mem_derivedOf_of_facts hF
  have haz₀ : ((GxSelf a * z₀ : ↥(Gx a)) : G) ∈ derivedOf (Gx a) := by
    rw [derivedOf]
    exact Subgroup.mem_map.mpr ⟨GxSelf a * z₀, hF.mem_commutator.2.2, rfl⟩
  rcases ht with ⟨k, hk, hkt⟩ | ⟨k, hk, hkt⟩
  · rw [← hkt]
    exact conj_mem_derivedOf (H := Gx a) hk hz₀
  · rw [← hkt]
    simpa [GxSelf] using conj_mem_derivedOf (H := Gx a) hk haz₀

end CFSG.EvenSporadicStandard.HNRecog.Section3
