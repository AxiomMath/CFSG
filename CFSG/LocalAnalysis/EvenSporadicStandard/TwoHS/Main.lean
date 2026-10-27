module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Iso

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem finite_of_mulEquiv {K C : Type} [Group K] [Group C] (e : K ≃* C) (h : Finite C) :
    Finite K :=
  Finite.of_equiv C e.symm.toEquiv

theorem IsHSCover.finite {H : Type} [Group H] {E : Subgroup H}
    (h : IsHSCover H E) : Finite H := by
  obtain ⟨e⟩ := h.quotient
  have hq : Finite (E ⧸ center E) :=
    finite_of_mulEquiv e CFSG.Sporadic.HS.fam_hs_simplicity.1
  have hz : Finite (center E) := Nat.finite_of_card_ne_zero (by rw [h.card_center]; norm_num)
  have hE : Finite E :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := center E)).symm
  have hidx : E.index ≠ 0 := fun h0 => by
    have := h.index_dvd_two
    rw [h0] at this
    exact absurd (Nat.eq_zero_of_zero_dvd this) (by norm_num)
  have : E.FiniteIndex := ⟨hidx⟩
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := E)).symm

theorem IsHSCover.card_mulAut_mul_card_centralizer_le
    {H : Type} [Group H]
    {E : Subgroup H} (h : IsHSCover H E) (hi : E.index = 2) :
    Nat.card (MulAut E) * Nat.card (centralizer (E : Set H)) ≤ Nat.card H := by
  have hperf := h.perfect
  have hfin := h.finite
  obtain ⟨e⟩ := h.quotient
  have h1 : Nat.card (MulAut E) ≤ 88704000 := by
    rw [← card_mulAut_of_isSporadic_hs h.quotient]
    exact Nat.card_le_card_of_injective _
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective E)
  have h2 : Nat.card (centralizer (E : Set H)) ≤ 2 := by
    rw [← h.card_center]
    refine Nat.card_le_card_of_injective
      (fun x : centralizer (E : Set H) => (⟨⟨x, h.centralizer_le x.2⟩, ?_⟩ : center E)) ?_
    · rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.1 x.2 y y.2)
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : center E => ((z : E) : H)) hxy)
  have h3 : Nat.card E = 88704000 := by
    have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center E)
    have hHS : Nat.card (Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
    rw [Nat.card_congr e.toEquiv, hHS, h.card_center] at h4
    omega
  have h5 := Subgroup.card_mul_index E
  rw [h3, hi] at h5
  calc Nat.card (MulAut E) * Nat.card (centralizer (E : Set H)) ≤ 88704000 * 2 :=
      Nat.mul_le_mul h1 h2
    _ = Nat.card H := by omega

theorem twoHSGivesHN_of_inputs
    (hR : HaradaHNRecognitionKP) (hSol : SolomonTwoHSCentralizer) (hHar : HaradaCentralizerShape)
    (hHN : HNCentralizerFacts) : TwoHSGivesHN := by
  intro G _ _ L h hZ hq
  have := h.simple
  obtain ⟨t, ht2, -, hcov⟩ := h.exists_isHSCover (hSol G L h hZ hq) hZ hq
  have hF5 := hHar G h.nonabelian t ht2 _ hcov
  obtain ⟨z₀, hz₀, E₂, hcov₂, hi₂, hsign⟩ := hHN
  have := hcov.normal
  have := hcov₂.normal
  have := hcov.finite
  have := hcov₂.finite
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_doubleCover_hs hcov.perfect hcov₂.perfect hcov.card_center
    hcov₂.card_center hcov.quotient hcov₂.quotient
  obtain ⟨v, hv, hv2⟩ := hF5.exists_outer_involution
  obtain ⟨ψ⟩ := exists_mulEquiv_of_outer_involution hF5.index_eq_two hi₂ hcov.centralizer_le φ
    (conjNormal_surjective_of_card_le (hcov₂.card_mulAut_mul_card_centralizer_le hi₂)) hv hv2 hsign
  exact hR z₀ hz₀ ⟨E₂, isComponent_of_isHSCover hcov₂⟩ G h.kProper t ht2 ⟨ψ⟩

end CFSG.EvenSporadicStandard.TwoHS
