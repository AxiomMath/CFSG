module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoNormalHullClass
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoNormalClosureImage
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoNormalHullData

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normal_hull_odd_quotient_ker (Q : Subgroup G) :
    let J := Subgroup.normalClosure (Q : Set G)
    (QuotientGroup.mk' (oddCore J)).ker = oddCore J :=
  QuotientGroup.ker_mk' _

theorem normal_hull_odd_quotient_ker_odd (Q : Subgroup G) :
    let J := Subgroup.normalClosure (Q : Set G)
    Odd (Nat.card (QuotientGroup.mk' (oddCore J)).ker) := by
  dsimp only
  rw [normal_hull_odd_quotient_ker]
  exact CFSG.ComponentClassification.OddCore.odd_card _

omit [Finite G] in
theorem normal_hull_odd_quotient_surjective (Q : Subgroup G) :
    let J := Subgroup.normalClosure (Q : Set G)
    Function.Surjective (QuotientGroup.mk' (oddCore J)) :=
  QuotientGroup.mk'_surjective _

theorem normal_hull_odd_quotient_corefree (Q : Subgroup G) :
    let J := Subgroup.normalClosure (Q : Set G)
    oddCore (J ⧸ oddCore J) = ⊥ :=
  CFSG.ComponentClassification.OddCore.quotient_corefree _

theorem normal_hull_odd_quotient_ker_le_normalizer (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    (QuotientGroup.mk' (oddCore J)).ker ≤
      Subgroup.normalizer (Q.subgroupOf J : Set J) := by
  dsimp only
  rw [normal_hull_odd_quotient_ker]
  exact normal_hull_odd_core_le_normalizer Q htight hodd hrank

theorem normal_hull_odd_quotient_Q_tightly_embedded (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    TightlyEmbedded ((Q.subgroupOf J).map (QuotientGroup.mk' (oddCore J))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  exact tightly_embedded_image_of_odd_kernel (QuotientGroup.mk' (oddCore J))
    (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
    (Q.subgroupOf J) (normal_hull_Q_tightly_embedded Q htight hodd)
    (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)
    (normal_hull_odd_quotient_ker_le_normalizer Q htight hodd hrank)

theorem normal_hull_odd_quotient_Q_odd_normalizer_overlaps (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    OddNormalizerOverlaps ((Q.subgroupOf J).map (QuotientGroup.mk' (oddCore J))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  exact odd_normalizer_overlaps_image (QuotientGroup.mk' (oddCore J))
    (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
    (Q.subgroupOf J) (normal_hull_Q_tightly_embedded Q htight hodd)
    (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)
    (normal_hull_odd_quotient_ker_le_normalizer Q htight hodd hrank)

theorem normal_hull_odd_quotient_Q_normalizer_map (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    let q := QuotientGroup.mk' (oddCore J)
    ((Subgroup.normalizer (Q : Set G)).subgroupOf J).map q =
      Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J)) := by
  dsimp only
  let J := Subgroup.normalClosure (Q : Set G)
  rw [← normal_hull_Q_normalizer Q htight hodd]
  exact odd_kernel_normalizer_map (QuotientGroup.mk' (oddCore J))
    (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
    (Q.subgroupOf J) (normal_hull_Q_tightly_embedded Q htight hodd)
    (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)
    (normal_hull_odd_quotient_ker_le_normalizer Q htight hodd hrank)

theorem normal_hull_odd_quotient_Q_normalizer_preimage (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    let q := QuotientGroup.mk' (oddCore J)
    (Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))).comap q =
      (Subgroup.normalizer (Q : Set G)).subgroupOf J := by
  dsimp only
  let J := Subgroup.normalClosure (Q : Set G)
  rw [← normal_hull_Q_normalizer Q htight hodd]
  exact odd_kernel_normalizer_preimage (QuotientGroup.mk' (oddCore J))
    (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
    (Q.subgroupOf J) (normal_hull_Q_tightly_embedded Q htight hodd)
    (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)
    (normal_hull_odd_quotient_ker_le_normalizer Q htight hodd hrank)

theorem normal_hull_odd_quotient_Q_nonnormal (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) (hnormal : ¬ Q.Normal) :
    let J := Subgroup.normalClosure (Q : Set G)
    ¬ ((Q.subgroupOf J).map (QuotientGroup.mk' (oddCore J))).Normal := by
  dsimp only
  let J := Subgroup.normalClosure (Q : Set G)
  intro hnormalImage
  exact normal_hull_Q_nonnormal Q htight hodd
    hnormal ((normality_iff_odd_kernel_image (QuotientGroup.mk' (oddCore J))
      (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
      (Q.subgroupOf J) (normal_hull_Q_tightly_embedded Q htight hodd)
      (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)
      (normal_hull_odd_quotient_ker_le_normalizer Q htight hodd hrank)).mpr hnormalImage)

theorem normal_hull_odd_quotient_Q_normalClosure_top (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let q := QuotientGroup.mk' (oddCore J)
    Subgroup.normalClosure ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J)) = ⊤ := by
  dsimp only
  let J := Subgroup.normalClosure (Q : Set G)
  let q := QuotientGroup.mk' (oddCore J)
  change Subgroup.normalClosure ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J)) = ⊤
  rw [← normal_closure_map q (normal_hull_odd_quotient_surjective Q),
    normal_hull_Q_normalClosure_top Q hodd hnormal z hzQ hz,
    Subgroup.map_top, MonoidHom.range_eq_top.mpr (normal_hull_odd_quotient_surjective Q)]

theorem normal_hull_strong_embedding_of_odd_core_quotient (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q)
    (himage :
      let J := Subgroup.normalClosure (Q : Set G)
      let q := QuotientGroup.mk' (oddCore J)
      fusionStronglyEmbedded
        (Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J)))) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  have h := strongly_embedded_preimage_of_odd_kernel (QuotientGroup.mk' (oddCore J))
    (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
    (Subgroup.normalizer ((Q.subgroupOf J).map (QuotientGroup.mk' (oddCore J)) :
      Set (J ⧸ oddCore J))) himage
  rwa [normal_hull_odd_quotient_Q_normalizer_preimage Q htight hodd hrank] at h

end CFSG.ComponentClassification.AschbacherTightEmbedding
