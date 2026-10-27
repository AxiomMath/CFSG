module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFourGroupHull

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] [Finite G]

theorem relative_index_sup_normal_dvd_card (Q R : Subgroup G) [R.Normal] :
    (Q.subgroupOf (Q ⊔ R)).index ∣ Nat.card R := by
  let J := Q ⊔ R
  have hQcard : Nat.card Q * Q.relIndex J = Nat.card J := by
    have h := (Q.subgroupOf J).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : Q ≤ J)).toEquiv] at h
    exact h
  have hRcard : Nat.card R * R.relIndex Q = Nat.card J := by
    have h := (R.subgroupOf J).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R ≤ J)).toEquiv] at h
    change Nat.card R * R.relIndex (Q ⊔ R) = Nat.card J at h
    rwa [Subgroup.relIndex_sup_right] at h
  have hIcard : Nat.card (R.subgroupOf Q) * R.relIndex Q = Nat.card Q :=
    (R.subgroupOf Q).card_mul_index
  have hcancel : R.relIndex Q * (Nat.card (R.subgroupOf Q) * Q.relIndex J) =
      R.relIndex Q * Nat.card R := by
    calc
      _ = (Nat.card (R.subgroupOf Q) * R.relIndex Q) * Q.relIndex J := by ac_rfl
      _ = Nat.card Q * Q.relIndex J := by rw [hIcard]
      _ = Nat.card R * R.relIndex Q := hQcard.trans hRcard.symm
      _ = _ := Nat.mul_comm _ _
  have hpositive : 0 < R.relIndex Q := Nat.pos_of_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := R.subgroupOf Q))
  have hcard : Nat.card (R.subgroupOf Q) * Q.relIndex J = Nat.card R :=
    Nat.eq_of_mul_eq_mul_left hpositive hcancel
  exact ⟨Nat.card (R.subgroupOf Q), hcard.symm.trans (Nat.mul_comm _ _)⟩

omit [Finite G] in
theorem normal_closure_le_sup_of_normalizer_factorization (Q R : Subgroup G) [R.Normal]
    (hfactor : ∀ g : G, ∃ h ∈ Subgroup.normalizer (Q : Set G), ∃ r ∈ R, g = h * r) :
    Subgroup.normalClosure (Q : Set G) ≤ Q ⊔ R := by
  have hnormal : (Q ⊔ R).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    obtain ⟨h, hh, r, hr, rfl⟩ := hfactor g
    exact (Subgroup.normalizer ((Q ⊔ R : Subgroup G) : Set G)).mul_mem
      (Subgroup.normalizer_le_normalizer_sup_normal hh)
      (Subgroup.le_normalizer ((le_sup_right : R ≤ Q ⊔ R) hr))
  let : (Q ⊔ R).Normal := hnormal
  exact Subgroup.normalClosure_le_normal (le_sup_left : Q ≤ Q ⊔ R)

theorem normal_hull_index_odd_of_rank_one_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hrank : twoRank (involutionPointHull z) ≤ 1) :
    Odd (Q.subgroupOf (Subgroup.normalClosure (Q : Set G))).index := by
  have hisolated := CFSG.ProperTwoGeneratedCore.involution_hull_rank_le_one_isolated hz hrank
  obtain ⟨_, hfactor⟩ := native_zStar_of_isolated_involution hz hisolated
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

theorem theorem_2_part_two_of_rank_one_point_hull (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hrank : twoRank (involutionPointHull z) ≤ 1) :
    Q.Normal ∨ fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G))) := by
  by_cases hnormal : Q.Normal
  · exact Or.inl hnormal
  · exact Or.inr (normal_hull_strong_embedding_of_odd_relative_index Q htight hodd hnormal
      (normal_hull_index_odd_of_rank_one_point_hull Q hodd z hzQ hz hrank))

end CFSG.ComponentClassification.AschbacherTightEmbedding
