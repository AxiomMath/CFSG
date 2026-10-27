module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingSplit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPointHallAssembly
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoRankReduction

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem theorem_2_part_two
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity)
    {G : Type} [Group G] [Finite G] (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) :
    Q.Normal ∨ fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G))) := by
  by_cases hnormal : Q.Normal
  · exact Or.inl hnormal
  by_cases hrank : twoRank Q ≤ 1
  · exact theorem_2_part_two_of_rank_one_Q Q htight hodd hrank
  have hrank2 : 2 ≤ twoRank Q := by omega
  right
  obtain ⟨P, z, hH, hzQ, hz, hzc, huniq, -, h2, -, -⟩ :=
    theorem_three_three_normal_hull_odd_quotient_hypotheses Q htight hodd hnormal hrank2
  let J := Subgroup.normalClosure (Q : Set G)
  let q := QuotientGroup.mk' (CFSG.oddCore J)
  let Hb := Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ CFSG.oddCore J))
  have hzb : orderOf (q z) = 2 := orderOf_map_of_odd q (normal_hull_odd_quotient_ker_odd Q) hz
  have hcentral : InvolutionPointCentralSylow (q z) := by
    obtain ⟨c, hc, hcz⟩ := hzc
    have hmem : q z ∈ (P : Subgroup (J ⧸ CFSG.oddCore J)) := hcz ▸ c.property
    refine ⟨P, hmem, ?_⟩
    have hceq : c = ⟨q z, hmem⟩ := Subtype.ext hcz
    exact hceq ▸ hc
  have h2b : CentralProductCentralizer Hb (q z) :=
    ⟨hcentral, fun t ht hzt hne => h2 t ht (Ne.symm hne) hzt⟩
  have hO : CFSG.oddCore (J ⧸ CFSG.oddCore J) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree J
  have hcore : CFSG.oddCore (involutionPointHull (q z)) = ⊥ :=
    normal_hull_odd_quotient_point_hull_corefree Q (z : G) hzQ
  have hrankL : 2 ≤ twoRank (involutionPointHull (q z)) :=
    two_le_twoRank_hull hzb hH huniq hcentral hO
  obtain ⟨u, -, e, hM, hmember⟩ :=
    pointHull_split_of_centralProductCentralizer himp hcov Hb (q z) hzb hH huniq h2b hcore hrankL
  exact normal_hull_strong_embedding_of_odd_quotient_point_split Q htight hodd hnormal hrank2
    (z : G) hzQ ((Subgroup.orderOf_coe z).trans hz) e _ hM hmember

end CFSG.ComponentClassification.AschbacherStrongEmbedding
