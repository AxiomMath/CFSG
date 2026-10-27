module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoQuotientClass

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

theorem normal_hull_odd_quotient_point_hull_split_second_equiv (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B]
    (e :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (oddCore J)
      involutionPointHull (q zJ) ≃* A × B) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    ∃ e' : involutionPointHull (q zJ) ≃* B, ∀ x, e' x = (e x).2 := by
  let J := Subgroup.normalClosure (Q : Set G)
  let QJ := Q.subgroupOf J
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  have hrankJ : 2 ≤ twoRank QJ := by
    rw [normal_hull_Q_twoRank]
    exact hrank
  exact point_hull_image_split_second_equiv QJ
    (normal_hull_Q_odd_normalizer_overlaps Q htight hodd)
    (normal_hull_Q_nonnormal Q htight hodd hnormal) hrankJ zJ hzQ
    ((Subgroup.orderOf_coe zJ).symm.trans hz) q
    (normal_hull_odd_quotient_surjective Q) e

theorem normal_hull_odd_quotient_point_hull_strong_embedding_of_split
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B] [Finite B]
    (e :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (oddCore J)
      involutionPointHull (q zJ) ≃* A × B)
    (M : Subgroup B) (hM : fusionStronglyEmbedded M)
    (hmember :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (oddCore J)
      ∀ x : involutionPointHull (q zJ),
        (e x).2 ∈ M ↔ (x : J ⧸ oddCore J) ∈
          Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    fusionStronglyEmbedded
      ((Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))).subgroupOf
        (involutionPointHull (q zJ))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  let Hq := Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))
  let Lq := involutionPointHull (q zJ)
  obtain ⟨e', he'⟩ := normal_hull_odd_quotient_point_hull_split_second_equiv
    Q htight hodd hnormal hrank z hzQ hz e
  have hmap : M.map e'.symm.toMonoidHom = Hq.subgroupOf Lq := by
    ext x
    constructor
    · rintro ⟨b, hb, hbx⟩
      have hexb : e' x = b := by
        rw [← hbx]
        exact e'.apply_symm_apply b
      apply (hmember x).mp
      rw [← he' x, hexb]
      exact hb
    · intro hx
      refine ⟨e' x, ?_, e'.symm_apply_apply x⟩
      rw [he' x]
      exact (hmember x).mpr hx
  change fusionStronglyEmbedded (Hq.subgroupOf Lq)
  rw [← hmap]
  exact hM.map_mulEquiv e'.symm

theorem normal_hull_point_hull_normalizer_map (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    (((Subgroup.normalizer (Q : Set G)).subgroupOf J).subgroupOf
      (involutionPointHull zJ)).map (pointHullHom q zJ) =
      (Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))).subgroupOf
        (involutionPointHull (q zJ)) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  let f := pointHullHom q zJ
  let H := (Subgroup.normalizer (Q : Set G)).subgroupOf J
  let Hq := Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))
  have hpre : Hq.comap q = H :=
    normal_hull_odd_quotient_Q_normalizer_preimage Q htight hodd hrank
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change q (x : J) ∈ Hq
    have hxH : (x : J) ∈ H := hx
    rw [← hpre] at hxH
    exact hxH
  · intro hy
    obtain ⟨x, rfl⟩ := pointHullHom_surjective q (normal_hull_odd_quotient_surjective Q) zJ y
    refine ⟨x, ?_, rfl⟩
    change (x : J) ∈ H
    rw [← hpre]
    exact hy

theorem normal_hull_point_hull_strong_embedding_of_odd_quotient
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q)
    (himage :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (oddCore J)
      fusionStronglyEmbedded
        ((Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))).subgroupOf
          (involutionPointHull (q zJ)))) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    fusionStronglyEmbedded
      (((Subgroup.normalizer (Q : Set G)).subgroupOf J).subgroupOf
        (involutionPointHull zJ)) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  let f := pointHullHom q zJ
  let H := (Subgroup.normalizer (Q : Set G)).subgroupOf J
  let C := H.subgroupOf (involutionPointHull zJ)
  have hker : f.ker ≤ C := by
    intro x hx
    have hxq : (x : J) ∈ q.ker := by
      rw [pointHullHom_ker] at hx
      exact hx
    have hxH : (x : J) ∈ Subgroup.normalizer (Q.subgroupOf J : Set J) :=
      normal_hull_odd_quotient_ker_le_normalizer Q htight hodd hrank hxq
    rw [normal_hull_Q_normalizer Q htight hodd] at hxH
    exact hxH
  apply strongly_embedded_of_odd_kernel_image f
    (pointHullHom_surjective q (normal_hull_odd_quotient_surjective Q) zJ)
    (pointHullHom_odd_ker q (normal_hull_odd_quotient_ker_odd Q) zJ) C hker
  rw [normal_hull_point_hull_normalizer_map Q htight hodd hrank z hzQ]
  exact himage

theorem involution_class_of_strong_embedding_in_point_hull (z : G)
    (hz : orderOf z = 2) (M : Subgroup (involutionPointHull z))
    (hM : fusionStronglyEmbedded M) (x : G) (hxL : x ∈ involutionPointHull z)
    (hx : orderOf x = 2) : x ∈ involutionPointClass z := by
  let L := involutionPointHull z
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  let xL : L := ⟨x, hxL⟩
  have hzL : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hz
  have hxLorder : orderOf xL = 2 := (Subgroup.orderOf_coe xL).symm.trans hx
  have hzI : IsInvolution zL :=
    ⟨(orderOf_eq_prime_iff.mp hzL).2, (orderOf_eq_prime_iff.mp hzL).1⟩
  have hxI : IsInvolution xL :=
    ⟨(orderOf_eq_prime_iff.mp hxLorder).2, (orderOf_eq_prime_iff.mp hxLorder).1⟩
  obtain ⟨g, hg⟩ := (native_strong_embedding_of_order_conditions hM).involutions_conjugate hzI hxI
  exact ⟨(g : G), congrArg L.subtype hg⟩

theorem normal_hull_point_hull_involution_mem_Q_of_embedding
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hM :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      fusionStronglyEmbedded
        (((Subgroup.normalizer (Q : Set G)).subgroupOf J).subgroupOf
          (involutionPointHull zJ))) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    ∀ x : J, x ∈ involutionPointHull zJ → orderOf x = 2 →
      (x ∈ (Subgroup.normalizer (Q : Set G)).subgroupOf J ↔ x ∈ Q.subgroupOf J) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  dsimp only
  intro x hxL hx
  have hxclass := involution_class_of_strong_embedding_in_point_hull zJ
    ((Subgroup.orderOf_coe zJ).symm.trans hz) _ hM x hxL hx
  have hxGclass : (x : G) ∈ involutionPointClass z :=
    (normal_hull_point_class_mem_iff Q hodd hnormal z hzQ hz x).mp hxclass
  exact class_mem_normalizer_iff_mem_Q Q hodd z hzQ hz x hxGclass

end CFSG.ComponentClassification.AschbacherTightEmbedding
