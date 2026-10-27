module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.InvQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiveGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.SixGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem gzClass_star (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    {t : G} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htA : ¬ IsConj a t) (htB : ¬ IsConj z t) {w : G}
    (hw : IsConj z w) (htw : t * w = w * t) :
    ∀ q ∈ Qz w, ⁅q, t⁆ ∈ Subgroup.zpowers w → ⁅q, t⁆ = 1 := by
  have h' : IsF5Type a w := isF5Type_of_isConj h (IsConj.refl a) hw
  have hF1' : Vert Fusion1Facts a w := hF1.of_isConj (IsConj.refl a) hw
  have hF2' : Vert Fusion2Facts a w := hF2.of_isConj (IsConj.refl a) hw
  have hF3' : Vert Fusion3Facts a w := hF3.of_isConj (IsConj.refl a) hw
  have hOrb' : Vert GzOrbitFacts a w := hOrb.of_isConj (IsConj.refl a) hw
  have hOrb'' : GzOrbitFacts a w := hOrb'.self
  let t' : ↥(Gx w) := ⟨t, mem_Gx.2 htw.symm⟩
  have htcoe : (t' : G) = t := rfl
  have ht2' : (t' : G) ^ 2 = 1 := by simpa only [htcoe] using ht2
  have ht'2 : t' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, htcoe] using ht2
  have htbar2 : (barOf w t') ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ht'2, QuotientGroup.mk_one]
  have htQ : t ∉ Qz w := by
    intro htQ
    rcases isConj_of_mem_Qz_involution hI hC h' hOrb'' htQ ht2 ht1 with hc | hc
    · exact htA hc
    · exact htB (hw.trans hc)
  have htbar1 : barOf w t' ≠ 1 := by
    intro h1
    exact htQ (htcoe ▸ (barOf_eq_one_iff t').1 h1)
  have h240 : Nat.card ↥(CbarCent w t') = 240 := by
    obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h'
    rcases involution_cases_of_mulEquiv e htbar2 htbar1 with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · exfalso
      have h120 : Nat.card ↥(CbarCent w t') = 120 := by simpa only [CbarCent] using hc
      rcases (gzClass_centralizes_two_A hI hC h' hF1' hF2' hF3' hOrb' t' ht2'
        (Or.inl h120)).2 with hconj | hconj
      · exact htA (htcoe ▸ hconj)
      · exact htB (hw.trans (htcoe ▸ hconj))
    · simpa only [CbarCent] using hc
    · exfalso
      have h32 : Nat.card ↥(CbarCent w t') = 32 := by simpa only [CbarCent] using hc
      rcases (gzClass_centralizes_two_A hI hC h' hF1' hF2' hF3' hOrb' t' ht2'
        (Or.inr h32)).2 with hconj | hconj
      · exact htA (htcoe ▸ hconj)
      · exact htB (hw.trans (htcoe ▸ hconj))
  obtain ⟨hTcard, hCcard⟩ := gzClass_centQ_card hI hC h' hF1' hF2' hF3' hOrb' t' htbar2 h240
  have hTcard' : Nat.card (centQtilde w t) = 2 ^ 5 := by
    simpa only [htcoe] using hTcard
  have hCcard' : Nat.card {q : G // q ∈ Qz w ∧ q * t = t * q} = 2 ^ 5 := by
    simpa only [htcoe] using hCcard ht2'
  have hTcard'' : (centQtilde w t).ncard = 2 ^ 5 := by
    rw [← Nat.card_coe_set_eq]
    exact hTcard'
  have hCcard'' : ({q : G | q ∈ Qz w ∧ q * t = t * q} : Set G).ncard = 2 ^ 5 := by
    rw [← Nat.card_coe_set_eq]
    exact hCcard'
  have hsub : {q : G | q ∈ Qz w ∧ q * t = t * q} ⊆ centQtilde w t := by
    rintro q ⟨hqQ, hqc⟩
    exact ⟨hqQ, by rw [commutatorElement_eq_one_iff_mul_comm.mpr hqc]; exact Subgroup.one_mem _⟩
  have hcardeq : (centQtilde w t).ncard =
      ({q : G | q ∈ Qz w ∧ q * t = t * q} : Set G).ncard := by
    rw [hTcard'', hCcard'']
  have heq : {q : G | q ∈ Qz w ∧ q * t = t * q} = centQtilde w t :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcardeq) (Set.toFinite _)
  intro q hqQ hq
  have hqT : q ∈ centQtilde w t := ⟨hqQ, hq⟩
  have hqC : q ∈ {q : G | q ∈ Qz w ∧ q * t = t * q} := by
    rw [heq]
    exact hqT
  exact commutatorElement_eq_one_iff_mul_comm.mpr hqC.2

end CFSG.EvenSporadicStandard.HNRecog.Section3
