module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoNormalHullQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoHullImage

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]

omit [Finite K] in
theorem odd_kernel_injective_on_elementary (f : G →* K)
    (hkerodd : Odd (Nat.card f.ker)) (E : Subgroup G)
    (hE : IsElemAbelian 2 E) : Function.Injective (f.domRestrict E) := by
  intro a b hab
  have hker : (a : G)⁻¹ * b ∈ f.ker := by
    change f ((a : G)⁻¹ * b) = 1
    rw [map_mul, map_inv]
    change (f.domRestrict E a)⁻¹ * f.domRestrict E b = 1
    rw [hab, inv_mul_cancel]
  have hmem : (a : G)⁻¹ * b ∈ E := E.mul_mem (E.inv_mem a.property) b.property
  have hone := square_one_eq_one_of_mem_odd_subgroup f.ker hkerodd hker (hE.2 _ hmem)
  exact Subtype.ext (inv_mul_eq_one.mp hone)

omit [Finite K] in
theorem odd_kernel_elementary_image_card (f : G →* K)
    (hkerodd : Odd (Nat.card f.ker)) (E : Subgroup G)
    (hE : IsElemAbelian 2 E) : Nat.card (E.map f) = Nat.card E := by
  have hinj : Function.Injective (f.subgroupMap E) := by
    intro a b hab
    exact odd_kernel_injective_on_elementary f hkerodd E hE
      (congrArg Subtype.val hab)
  exact Nat.card_congr (Equiv.ofBijective (f.subgroupMap E)
    ⟨hinj, f.subgroupMap_surjective E⟩).symm

theorem odd_kernel_image_pRank_le (f : G →* K)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G) :
    CFSG.Open.pRank 2 Q ≤ CFSG.Open.pRank 2 (Q.map f) := by
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.ComponentClassification.TwoRankTransport.witness Q
  apply CFSG.ComponentClassification.TwoRankTransport.rank_le (Q.map f) (E.map f)
    (Subgroup.map_mono hEQ)
    (CFSG.ComponentClassification.TwoRankTransport.elementary_map f E hE)
  rw [odd_kernel_elementary_image_card f hkerodd E hE]
  exact hcard

theorem odd_kernel_image_twoRank_le (f : G →* K)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G) :
    twoRank Q ≤ twoRank (Q.map f) := by
  rw [CFSG.ComponentClassification.TwoRankTransport.subgroup,
    CFSG.ComponentClassification.TwoRankTransport.subgroup]
  exact odd_kernel_image_pRank_le f hkerodd Q

theorem normal_hull_odd_quotient_Q_twoRank_le (Q : Subgroup G) :
    let J := Subgroup.normalClosure (Q : Set G)
    twoRank Q ≤ twoRank ((Q.subgroupOf J).map (QuotientGroup.mk' (oddCore J))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  have h := odd_kernel_image_twoRank_le (QuotientGroup.mk' (oddCore J))
    (normal_hull_odd_quotient_ker_odd Q) (Q.subgroupOf J)
  rw [normal_hull_Q_twoRank] at h
  exact h

theorem normal_hull_odd_quotient_point_hull_perfect (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    Group.IsPerfect (involutionPointHull ((QuotientGroup.mk' (oddCore J)) zJ)) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  let : Group.IsPerfect (involutionPointHull zJ) :=
    normal_hull_point_hull_perfect Q hodd hnormal hrank z hzQ hz
  exact Group.IsPerfect.ofSurjective (f := pointHullHom q zJ)
    (pointHullHom_surjective q (normal_hull_odd_quotient_surjective Q) zJ)

end CFSG.ComponentClassification.AschbacherTightEmbedding
