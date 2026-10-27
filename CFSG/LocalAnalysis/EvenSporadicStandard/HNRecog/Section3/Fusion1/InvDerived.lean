module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem mem_derivedOf_self {G : Type} [Group G] {a z : G} (hF1 : Fusion1Facts a z) :
    a ∈ derivedOf (Gx a) := by
  obtain ⟨z₀, b, u, hF, _⟩ := hF1.rep_z
  refine mem_derivedOf_iff.mpr ⟨self_mem_Gx a, ?_⟩
  simpa [GxSelf] using hF.mem_commutator.1

theorem inv_mem_derivedOf_cases (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) {t : G} (ht : t ∈ derivedOf (Gx a))
    (ht2 : orderOf t = 2) :
    t = a ∨ (IsConj z t ∧ IsConj a (a * t) ∧ a ∈ Qz t) ∨ (IsConj a t ∧ IsConj z (a * t)) := by
  obtain ⟨htG, htC⟩ := mem_derivedOf_iff.mp ht
  obtain ⟨z₀, b, u, hF, hz, haz, _, haQ, _⟩ := hF1.rep_z
  let t' : ↥(Gx a) := ⟨t, htG⟩
  have ht2' : orderOf t' = 2 := (Subgroup.orderOf_mk t htG).trans ht2
  have ha2 : a * a = 1 := by
    rw [← pow_two, ← h.orderOf_a]
    exact pow_orderOf_eq_one a
  have hmem_of_conj : ∀ c x : ↥(Gx a), c ∈ commutator ↥(Gx a) → IsConj c x →
      x ∈ commutator ↥(Gx a) := by
    intro c x hc hconj
    rw [isConj_iff] at hconj
    obtain ⟨g, hg⟩ := hconj
    have := (inferInstance : (commutator ↥(Gx a)).Normal).conj_mem c hc g
    rwa [hg] at this
  obtain ⟨i, hi⟩ := hF.involution_cover t' ht2'
  fin_cases i
  ·
    change IsConj (GxSelf a) t' at hi
    have hself_center : GxSelf a ∈ Subgroup.center ↥(Gx a) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp g.2
    left
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    have hfix : c * GxSelf a * c⁻¹ = GxSelf a := by
      rw [Subgroup.mem_center_iff.mp hself_center c, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix] at hc
    exact congrArg Subtype.val hc.symm
  ·
    change IsConj z₀ t' at hi
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    have hcG : (c : G) * (z₀ : G) * (c : G)⁻¹ = t := by
      have := congrArg Subtype.val hc
      simpa [t'] using this
    have hca : (c : G) * a * (c : G)⁻¹ = a := by
      rw [← mem_Gx.mp c.2, mul_assoc, mul_inv_cancel, mul_one]
    have hconjG : IsConj (z₀ : G) t := isConj_iff.mpr ⟨(c : G), hcG⟩
    refine Or.inr (Or.inl ⟨hz.trans hconjG, ?_, ?_⟩)
    · have hziel : IsConj (a * (z₀ : G)) (a * t) :=
        isConj_iff.mpr ⟨(c : G), by
          calc (c : G) * (a * (z₀ : G)) * (c : G)⁻¹
              = ((c : G) * a * (c : G)⁻¹) * ((c : G) * (z₀ : G) * (c : G)⁻¹) := by group
            _ = a * t := by rw [hca, hcG]⟩
      exact haz.trans hziel
    · have hmem : (c : G) * a * (c : G)⁻¹ ∈ Qz ((c : G) * (z₀ : G) * (c : G)⁻¹) :=
        Qz_conj_mem (c : G) haQ
      rwa [hca, hcG] at hmem
  ·
    change IsConj (GxSelf a * z₀) t' at hi
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    have hcG : (c : G) * (a * (z₀ : G)) * (c : G)⁻¹ = t := by
      have := congrArg Subtype.val hc
      simpa [t', GxSelf] using this
    have hconjG : IsConj (a * (z₀ : G)) t := isConj_iff.mpr ⟨(c : G), hcG⟩
    have hz0eq : a * t = (c : G) * (z₀ : G) * (c : G)⁻¹ := by
      calc a * t = a * ((c : G) * (a * (z₀ : G)) * (c : G)⁻¹) := by rw [hcG]
        _ = (a * (c : G)) * a * (z₀ : G) * (c : G)⁻¹ := by group
        _ = ((c : G) * a) * a * (z₀ : G) * (c : G)⁻¹ := by rw [mem_Gx.mp c.2]
        _ = (c : G) * (a * a) * (z₀ : G) * (c : G)⁻¹ := by group
        _ = (c : G) * (z₀ : G) * (c : G)⁻¹ := by rw [ha2, mul_one]
    refine Or.inr (Or.inr ⟨haz.trans hconjG, ?_⟩)
    exact hz.trans (isConj_iff.mpr ⟨(c : G), hz0eq.symm⟩)
  ·
    change IsConj b t' at hi
    exact absurd (hmem_of_conj t' b htC hi.symm) hF.not_mem_commutator.1
  ·
    change IsConj u t' at hi
    exact absurd (hmem_of_conj t' u htC hi.symm) hF.not_mem_commutator.2

end CFSG.EvenSporadicStandard.HNRecog.Section3
