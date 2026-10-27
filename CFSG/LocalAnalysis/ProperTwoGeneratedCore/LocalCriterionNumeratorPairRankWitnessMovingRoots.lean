module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankWitnessPartnerChoice
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankWitnessTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem numeratorPairRank_noncentral_class_has_moved_root
    (H : Subgroup G) (z u v : G)
    (hmove : v ∉ Subgroup.centralizer (numeratorPairRankPointClass H z u)) :
    ∃ x ∈ numeratorPairRankPointClass H z u, rightConjugateElem x v ≠ x := by
  by_contra hnone
  push Not at hnone
  apply hmove
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have heq := congrArg (fun a : G => v * a) (hnone x hx)
  simpa only [rightConjugateElem, mul_assoc, mul_inv_cancel_left] using heq

variable [Finite G]

theorem original_high_rank_selected_both_moving_roots
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : FullPointPairGeneration H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    ∃ u v z₀ : G,
      u ∈ pairPointStabilizer H beta ∧ orderOf u = 2 ∧ Commute u t ∧
      v ∈ pairPointStabilizer H beta ∧ orderOf v = 2 ∧ v ≠ u ∧
      Commute u v ∧ Commute v t ∧ Commute u z₀ ∧ Commute v z₀ ∧
      (∀ w : G, w ∈ pairPointStabilizer H beta → orderOf w = 2 → Commute w t →
        Nat.card (numeratorPairRankPointClass H z w) ≤
          Nat.card (numeratorPairRankPointClass H z u)) ∧
      IsElemAbelian 2 (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
      Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) = 4 ∧
      z₀ ∈ conjugacyWithin H z ∧
      z₀ ∈ Subgroup.centralizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) ∧
      t ∈ Subgroup.centralizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) ∧
      MinimalInvolutionPointLocalFailure H z₀ ∧
      conjugacyWithin H z₀ = conjugacyWithin H z ∧
      (∀ w : G, numeratorPairRankPointClass H z₀ w = numeratorPairRankPointClass H z w) ∧
      (∀ w : G, localInvolutionPointHull z₀ w = localInvolutionPointHull z w) ∧
      (∀ gamma : rightCosetSpace H,
        rightPairFlipFiber H z₀ gamma = rightPairFlipFiber H z gamma) ∧
      Subgroup.zpowers z₀ ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤ ∧
      (¬ numeratorPairRankPointClass H z v ⊆ numeratorPairRankPointClass H z u) ∧
      v ∉ Subgroup.centralizer (numeratorPairRankPointClass H z u) ∧
      u ∉ Subgroup.centralizer (numeratorPairRankPointClass H z v) ∧
      (∃ x ∈ numeratorPairRankPointClass H z u, rightConjugateElem x v ≠ x) ∧
      (∃ x ∈ numeratorPairRankPointClass H z v, rightConjugateElem x u ≠ x) := by
  obtain ⟨u, v, z₀, huB, hu, hut, hvB, hv, hvu, huv, hvt, hmax,
    _helem, _hcard, hz₀, hz₀W, htW, h₀, hpoint, hclasses, hhulls, hgen₀⟩ :=
    original_high_rank_selected_witness_transport h hgen hbeta ht hrank
  obtain ⟨_h₀, _hclass, _hhull, _hpoint, _hclasses, _hhulls, hflips⟩ :=
    original_selected_point_root_transport h hz₀
  have ht₀ : t ∈ rightPairFlipFiber H z₀ beta := by
    rw [hflips beta]
    exact ht
  have hmax₀ : ∀ w : G, w ∈ pairPointStabilizer H beta → orderOf w = 2 → Commute w t →
      Nat.card (numeratorPairRankPointClass H z₀ w) ≤
        Nat.card (numeratorPairRankPointClass H z₀ u) := by
    intro w hwB hw hwt
    rw [hclasses w, hclasses u]
    exact hmax w hwB hw hwt
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h₀
  let : IsSimpleGroup G := hsimple
  obtain ⟨S₀, hz₀S, hz₀center⟩ := h₀.central_sylow
  obtain ⟨w, _hchoice, hwB, hw, hwu, huw, hwt, hjoin, helem, hcard,
    hnonnested, hwmove, humove, _hcommon, _hconj⟩ :=
    original_maximum_four_group_select_both_moving_roots hnonab h₀.local_datum
      S₀ hz₀S hz₀center hbeta ht₀ hgen₀ u v huB hu hvB hv hvu huv hut hvt hz₀W hmax₀
  have hz₀W' : z₀ ∈ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := by
    rw [hjoin]
    exact hz₀W
  have htW' : t ∈ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := by
    rw [hjoin]
    exact htW
  have huz₀ : Commute u z₀ := Subgroup.mem_centralizer_iff.mp hz₀W' u
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hwz₀ : Commute w z₀ := Subgroup.mem_centralizer_iff.mp hz₀W' w
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
  rw [hclasses w, hclasses u] at hnonnested
  rw [hclasses u] at hwmove
  rw [hclasses w] at humove
  exact ⟨u, w, z₀, huB, hu, hut, hwB, hw, hwu, huw, hwt, huz₀, hwz₀, hmax,
    helem, hcard, hz₀, hz₀W', htW', h₀, hpoint, hclasses, hhulls, hflips, hgen₀,
    hnonnested, hwmove, humove,
    numeratorPairRank_noncentral_class_has_moved_root H z u w hwmove,
    numeratorPairRank_noncentral_class_has_moved_root H z w u humove⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
