module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoRankOne

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.TwoRankLowerBound.Helpers
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] [Finite G]

theorem involution_isolated_of_rank_one_Q (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hrank : twoRank Q ≤ 1)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    ∀ g : G, Commute (g⁻¹ * z * g) z → g⁻¹ * z * g = z := by
  intro g hcommute
  have hgH : g ∈ Subgroup.normalizer (Q : Set G) :=
    (involution_conjugate_mem_normalizer_iff Q hodd z hzQ hz g).mp
      (involution_centralizer_le_normalizer Q hodd z hzQ hz
        (Subgroup.mem_centralizer_singleton_iff.mpr hcommute.eq))
  have hconjQ := (involution_conjugate_mem_Q_iff Q hodd z hzQ hz g).mpr hgH
  have hconjorder : orderOf (g⁻¹ * z * g) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using
      ((MulAut.conj g⁻¹).orderOf_eq z).trans hz
  have hcommuteQ : Commute (⟨g⁻¹ * z * g, hconjQ⟩ : Q) (⟨z, hzQ⟩ : Q) :=
    Subtype.ext hcommute.eq
  exact congrArg Subtype.val (commuting_involutions_eq_of_twoRank_le_one Q hrank
    ⟨g⁻¹ * z * g, hconjQ⟩ ⟨z, hzQ⟩
    ((Subgroup.orderOf_coe _).symm.trans hconjorder)
    ((Subgroup.orderOf_coe _).symm.trans hz) hcommuteQ)

theorem normal_hull_index_odd_of_rank_one_Q (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hrank : twoRank Q ≤ 1)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    Odd (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))).index := by
  obtain ⟨_, hfactor⟩ := native_zStar_of_isolated_involution hz
    (involution_isolated_of_rank_one_Q Q hodd hrank z hzQ hz)
  let R := CFSG.oddCore G
  have hL : Subgroup.normalClosure (Q : Set G) ≤ Q ⊔ R :=
    normal_closure_le_sup_of_normalizer_factorization Q R (by
      intro g
      obtain ⟨c, hc, r, hr, hcr⟩ := hfactor g
      exact ⟨c, involution_centralizer_le_normalizer Q hodd z hzQ hz hc, r, hr, hcr⟩)
  have hindex : Odd (Q.subgroupOf (Q ⊔ R)).index :=
    (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      (relative_index_sup_normal_dvd_card Q R)
  have hdiv : Q.relIndex (Subgroup.normalClosure (Q : Set G)) ∣ Q.relIndex (Q ⊔ R) :=
    ⟨(Subgroup.normalClosure (Q : Set G)).relIndex (Q ⊔ R),
      (Subgroup.relIndex_mul_relIndex Q _ _ Subgroup.le_normalClosure hL).symm⟩
  exact hindex.of_dvd_nat hdiv

theorem theorem_2_part_two_of_rank_one_Q (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : twoRank Q ≤ 1) :
    Q.Normal ∨ fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G))) := by
  by_cases hnormal : Q.Normal
  · exact Or.inl hnormal
  · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2
      (even_iff_two_dvd.mp htight.1)
    exact Or.inr (normal_hull_strong_embedding_of_odd_relative_index Q htight hodd hnormal
      (normal_hull_index_odd_of_rank_one_Q Q hodd hrank z z.property
        ((Subgroup.orderOf_coe z).trans hz)))

end CFSG.ComponentClassification.AschbacherTightEmbedding
