module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

theorem pair_odd_core_normalized
    (H : Subgroup G) (a b : pointRightCosetSpace H)
    (u t : G) (ht : orderOf t = 2)
    (huD : u ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    (hflip : pointRightCosetMul H a t = b) :
    let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
    let J := (oddCore D).map D.subtype
    J ≤ D ∧ Odd (Nat.card J) ∧
      denominatorFourGroup u t ≤ Subgroup.normalizer (J : Set G) := by
  let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let J := (oddCore D).map D.subtype
  have huJ : u ∈ Subgroup.normalizer (J : Set G) :=
    normalizer_normalizes_oddCore_image D (D.le_normalizer huD)
  have htJ : t ∈ Subgroup.normalizer (J : Set G) :=
    normalizer_normalizes_oddCore_image D (right_pair_flip_normalizes H t ht a b hflip)
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · change Odd (Nat.card ((oddCore D).map D.subtype : Subgroup G))
    rw [Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card D
  · rw [denominatorFourGroup_eq]
    exact sup_le (Subgroup.zpowers_le.mpr huJ) (Subgroup.zpowers_le.mpr htJ)

theorem distinguished_pair_odd_core_four_group_inputs
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (t : G) (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H a t = b)
    (u : G) (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) :
    let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
    let J := (oddCore D).map D.subtype
    let V := denominatorFourGroup u t
    u ≠ t ∧ orderOf t = 2 ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      J ≤ D ∧ Odd (Nat.card J) ∧ V ≤ Subgroup.normalizer (J : Set G) := by
  have ht : orderOf t = 2 := order_two_of_mem_pointClass h.distinguished_order htclass
  have hne := (commuting_pair_product_geometry H a b hab u t hu ht hut huD hflip).1
  obtain ⟨hV, hVcard, _⟩ := commuting_distinct_involutions_four_group hu ht hut hne.symm
  obtain ⟨hJD, hJodd, hVN⟩ := pair_odd_core_normalized H a b u t ht huD hflip
  rw [← denominatorFourGroup_eq] at hV hVcard
  exact ⟨hne, ht, hV, hVcard, hJD, hJodd, hVN⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
