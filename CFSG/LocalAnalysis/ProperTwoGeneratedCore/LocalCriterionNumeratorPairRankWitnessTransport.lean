module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankWitnessSelection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalIdentification

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem numeratorPairRankPointClass_at_class_member
    {H : Subgroup G} {z z₀ : G} (hz₀ : z₀ ∈ involutionPointClass z) (w : G) :
    numeratorPairRankPointClass H z₀ w = numeratorPairRankPointClass H z w := by
  unfold numeratorPairRankPointClass
  rw [pointClass_eq_of_mem hz₀]

theorem numeratorPairRankLocalHull_at_class_member
    {z z₀ : G} (hz₀ : z₀ ∈ involutionPointClass z) (w : G) :
    localInvolutionPointHull z₀ w = localInvolutionPointHull z w := by
  unfold localInvolutionPointHull
  rw [pointClass_eq_of_mem hz₀]

variable [Finite G]

theorem original_selected_point_root_transport
    {H : Subgroup G} {z z₀ : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hz₀ : z₀ ∈ conjugacyWithin H z) :
    MinimalInvolutionPointLocalFailure H z₀ ∧
      involutionPointClass z₀ = involutionPointClass z ∧
      involutionPointHull z₀ = involutionPointHull z ∧
      conjugacyWithin H z₀ = conjugacyWithin H z ∧
      (∀ w : G, numeratorPairRankPointClass H z₀ w = numeratorPairRankPointClass H z w) ∧
      (∀ w : G, localInvolutionPointHull z₀ w = localInvolutionPointHull z w) ∧
      ∀ beta : rightCosetSpace H,
        rightPairFlipFiber H z₀ beta = rightPairFlipFiber H z beta := by
  obtain ⟨h₀, hclass, hhull⟩ := minimalLocalFailure_at_point_class_member h hz₀
  have hz₀class : z₀ ∈ involutionPointClass z := by
    rw [← original_point_class_intersection_eq_conjugacyWithin h.local_datum] at hz₀
    exact hz₀.1
  have hpoint : conjugacyWithin H z₀ = conjugacyWithin H z := by
    rw [← original_point_class_intersection_eq_conjugacyWithin h₀.local_datum,
      ← original_point_class_intersection_eq_conjugacyWithin h.local_datum, hclass]
  refine ⟨h₀, hclass, hhull, hpoint,
    numeratorPairRankPointClass_at_class_member hz₀class,
    numeratorPairRankLocalHull_at_class_member hz₀class, ?_⟩
  intro beta
  unfold rightPairFlipFiber
  rw [hclass]

theorem original_selected_point_root_pair_generation
    {H : Subgroup G} {z z₀ : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : FullPointPairGeneration H z) (hz₀ : z₀ ∈ conjugacyWithin H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    Subgroup.zpowers z₀ ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤ := by
  obtain ⟨h₀, hclass, _hhull⟩ := minimalLocalFailure_at_point_class_member h hz₀
  have hz₀class : z₀ ∈ involutionPointClass z := by
    rw [← original_point_class_intersection_eq_conjugacyWithin h.local_datum] at hz₀
    exact hz₀.1
  have hgen₀ := fullPointPairGeneration_at_class_member hgen hz₀class
  have ht₀ : t ∈ rightPairFlipFiber H z₀ beta := by
    simpa only [rightPairFlipFiber, hclass] using ht
  exact fullPointPairGeneration_base h₀.local_datum hgen₀ beta hbeta t ht₀

theorem original_high_rank_selected_witness_transport
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : FullPointPairGeneration H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    ∃ u v z₀ : G,
      u ∈ pairPointStabilizer H beta ∧ orderOf u = 2 ∧ Commute u t ∧
      v ∈ pairPointStabilizer H beta ∧ orderOf v = 2 ∧ v ≠ u ∧
      Commute u v ∧ Commute v t ∧
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
      Subgroup.zpowers z₀ ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤ := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨_hindex, u, v, z₀, huB, hu, hut, hvB, hv, hvu, huv, hvt,
    hmax, hW, hcardW, hz₀, hz₀W, htW⟩ :=
    original_pair_maximum_involution_four_group_and_common_root
      h.local_datum S hzS hzcenter hbeta ht hrank
  obtain ⟨h₀, _hclass, _hhull, hpoint, hclasses, hhulls, _hflips⟩ :=
    original_selected_point_root_transport h hz₀
  exact ⟨u, v, z₀, huB, hu, hut, hvB, hv, hvu, huv, hvt, hmax, hW, hcardW,
    hz₀, hz₀W, htW, h₀, hpoint, hclasses, hhulls,
    original_selected_point_root_pair_generation h hgen hz₀ hbeta ht⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
