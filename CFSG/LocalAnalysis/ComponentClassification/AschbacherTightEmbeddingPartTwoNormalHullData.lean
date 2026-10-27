module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoDescent
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoOddCore

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normal_hull_Q_card (Q : Subgroup G) :
    Nat.card (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))) = Nat.card Q :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalClosure).toEquiv

omit [Finite G] in
theorem normal_hull_Q_even (Q : Subgroup G) (htight : TightlyEmbedded Q) :
    Even (Nat.card (Q.subgroupOf (Subgroup.normalClosure (Q : Set G)))) := by
  rw [normal_hull_Q_card]
  exact htight.1

theorem normal_hull_Q_normalizer (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) :
    Subgroup.normalizer
      (Q.subgroupOf (Subgroup.normalClosure (Q : Set G)) :
        Set (Subgroup.normalClosure (Q : Set G))) =
    (Subgroup.normalizer (Q : Set G)).subgroupOf
      (Subgroup.normalClosure (Q : Set G)) :=
  normalizer_intersection_eq Q _ hodd (normal_hull_Q_even Q htight)

theorem normal_hull_Q_tightly_embedded (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) :
    TightlyEmbedded (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))) :=
  tightly_embedded_intersection Q _ htight hodd (normal_hull_Q_even Q htight)

theorem normal_hull_Q_odd_normalizer_overlaps (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) :
    OddNormalizerOverlaps (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))) :=
  odd_normalizer_overlaps_intersection Q _ hodd (normal_hull_Q_even Q htight)

theorem normal_hull_Q_nonnormal (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) :
    ¬ (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))).Normal := by
  intro hnormalJ
  apply normal_hull_normalizer_proper Q htight hodd hnormal
  rw [← normal_hull_Q_normalizer Q htight hodd]
  exact Subgroup.normalizer_eq_top_iff.mpr hnormalJ

theorem normal_hull_odd_core (Q : Subgroup G) :
    oddCore (Subgroup.normalClosure (Q : Set G)) =
      (oddCore G).subgroupOf (Subgroup.normalClosure (Q : Set G)) := by
  let J := Subgroup.normalClosure (Q : Set G)
  apply Subgroup.map_injective J.subtype_injective
  change (oddCore J).map J.subtype = ((oddCore G).subgroupOf J).map J.subtype
  have hcore : (oddCore J).map J.subtype = J ⊓ oddCore G :=
    CFSG.ComponentClassification.OddCore.normal_intersection G J
  rw [hcore, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem normal_hull_odd_core_le_normalizer (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) :
    oddCore (Subgroup.normalClosure (Q : Set G)) ≤
      Subgroup.normalizer
        (Q.subgroupOf (Subgroup.normalClosure (Q : Set G)) :
          Set (Subgroup.normalClosure (Q : Set G))) := by
  rw [normal_hull_odd_core Q, normal_hull_Q_normalizer Q htight hodd]
  intro x hx
  exact oddCore_le_normalizer_of_rank_two_Q Q hodd hrank hx

end CFSG.ComponentClassification.AschbacherTightEmbedding
