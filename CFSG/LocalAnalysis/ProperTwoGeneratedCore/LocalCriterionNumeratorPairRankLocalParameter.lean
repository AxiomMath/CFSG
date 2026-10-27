module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalIdentification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorParameter

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_local_point_class_card_at_exponent
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z)
    (hescape : ¬ Subgroup.centralizer ({w} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z w))
    (hcentral : CFSG.oddCore (localInvolutionPointHull z w) ≤
      Subgroup.center (localInvolutionPointHull z w))
    (a : ℕ) (ha : 2 ≤ a)
    (hAt : IsSimpleBenderGroupAtExponent a
      (localInvolutionPointHull z w ⧸ CFSG.oddCore (localInvolutionPointHull z w))) :
    Nat.card ↥(conjugacyWithin H z ∩
      (Subgroup.centralizer ({w} : Set G) : Set G)) = 2 ^ a - 1 := by
  let L := localInvolutionPointHull z w
  let P := H.subgroupOf L
  let f := QuotientGroup.mk' (CFSG.oddCore L)
  let B := P.map f
  obtain ⟨_hmodel, hcore, hB⟩ :=
    original_local_hull_native_model_and_borel h w hw hwz hescape hrank
  obtain ⟨i, _hi, hparameter⟩ :=
    simpleBender_borel_exact_parameter_at_exponent a ha hAt
  have hcount := (hparameter B hB).2
  have hkerP : f.ker ≤ P := by
    rw [QuotientGroup.ker_mk']
    exact hcore
  have hPcomap : P = B.comap f := by
    exact (Subgroup.comap_map_eq_self hkerP).symm
  have hodd : Odd (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hkercentral : f.ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hcentral
  have hpointcount : Nat.card {x : L // x ∈ P ∧ IsInvolution x} = 2 ^ a - 1 := by
    rw [hPcomap]
    exact (whole_involution_card_comap_of_central_odd_kernel f
      (QuotientGroup.mk'_surjective (CFSG.oddCore L)) hodd hkercentral B).trans hcount
  have hset : conjugacyWithin H z ∩
      (Subgroup.centralizer ({w} : Set G) : Set G) =
      involutionPointClass z ∩
        (Subgroup.centralizer ({w} : Set G) : Set G) ∩ (H : Set G) := by
    rw [← original_point_class_intersection_eq_conjugacyWithin h]
    ext x
    change ((x ∈ involutionPointClass z ∧ x ∈ H) ∧
      x ∈ Subgroup.centralizer ({w} : Set G)) ↔
      ((x ∈ involutionPointClass z ∧ x ∈ Subgroup.centralizer ({w} : Set G)) ∧ x ∈ H)
    exact ⟨fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩,
      fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩⟩
  rw [hset, ← original_point_involution_intersection_card h w hwz
    (h.local_embedding w hw hwz hescape)]
  exact hpointcount

theorem original_rank_two_entire_local_inversion_cyclic_of_fixed_root_card
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z w)) :
    ∃ J : Subgroup G,
      (J : Set G) = {x : G | x ∈ pairOddCore H beta ⊓
        Subgroup.centralizer ({w} : Set G) ∧ rightConjugateElem x t = x⁻¹} ∧
      IsCyclic J ∧ Nat.card J = Nat.card ↥(conjugacyWithin H z ∩
        (Subgroup.centralizer ({w} : Set G) : Set G)) := by
  obtain ⟨a, ha, hAt, J, hJset, hJcyclic, hJcard⟩ :=
    original_rank_two_entire_local_inversion_cyclic h hcomm hsmallerR1
      S hzS hzcenter beta hbeta t ht w hw hwz hwt hrank
  have hescape : ¬ Subgroup.centralizer ({w} : Set G) ≤ H :=
    fun hle => pair_flip_not_mem_point hbeta ht
      (hle (Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm.eq))
  have hcentral := original_local_hull_entire_oddCore_central
    h hcomm hsmallerR1 w hw hwz hescape hrank
  have hdelta := original_local_point_class_card_at_exponent
    h.local_datum w hw hwz hescape hrank hcentral a ha hAt
  exact ⟨J, hJset, hJcyclic, hJcard.trans hdelta.symm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
