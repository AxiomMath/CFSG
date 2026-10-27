module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPointHallTransport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoHullExtension
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoHullEmbedding

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

theorem normal_hull_point_hull_normalizer_equiv_map (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    (((Subgroup.normalizer (Q : Set G)).subgroupOf J).subgroupOf
      (involutionPointHull zJ)).map
        (normalHullPointHullEquiv Q hodd hnormal z hzQ hz).toMonoidHom =
      (Subgroup.normalizer (Q : Set G)).subgroupOf (involutionPointHull z) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let H := Subgroup.normalizer (Q : Set G)
  let e := normalHullPointHullEquiv Q hodd hnormal z hzQ hz
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change ((e.symm x : J) : G) ∈ H
    have he : (e (e.symm x) : G) = ((e.symm x : J) : G) :=
      normalHullPointHullEquiv_apply Q hodd hnormal z hzQ hz (e.symm x)
    rw [e.apply_symm_apply] at he
    exact he ▸ hx

theorem normal_hull_strong_embedding_of_corefree_point_embedding
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hM : CFSG.BenderSuzuki.IsStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (involutionPointHull z)))
    (hcore : CFSG.oddCore (involutionPointHull z) = ⊥) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf
        (Subgroup.normalClosure (Q : Set G))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let H := Subgroup.normalizer (Q : Set G)
  let C := (H.subgroupOf J).subgroupOf (involutionPointHull zJ)
  let e := normalHullPointHullEquiv Q hodd hnormal z hzQ hz
  have hmap : C.map e.toMonoidHom = H.subgroupOf (involutionPointHull z) :=
    normal_hull_point_hull_normalizer_equiv_map Q hodd hnormal z hzQ hz
  have hinverse : (H.subgroupOf (involutionPointHull z)).map e.symm.toMonoidHom = C := by
    rw [← hmap, Subgroup.map_map]
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id (involutionPointHull zJ) := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [hid, Subgroup.map_id]
  have hC : fusionStronglyEmbedded C := by
    have h := (order_strong_embedding_of_native hM).map_mulEquiv e.symm
    rwa [hinverse] at h
  have hindex := normal_hull_point_hull_odd_index_of_corefree_point_strong_embedding
    Q hodd hnormal hrank z hzQ hz hM hcore
  exact normal_hull_strong_embedding_of_point_hull_odd_index
    Q htight hodd hnormal z hzQ hz hindex hC

theorem strong_embedding_of_corefree_point_embedding_of_normal_generation
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hM : CFSG.BenderSuzuki.IsStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (involutionPointHull z)))
    (hcore : CFSG.oddCore (involutionPointHull z) = ⊥)
    (hgen : Subgroup.normalClosure (Q : Set G) = ⊤) :
    fusionStronglyEmbedded (Subgroup.normalizer (Q : Set G)) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let H := Subgroup.normalizer (Q : Set G)
  let e : J ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hmap : (H.subgroupOf J).map e.toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      let a : J := ⟨x, by change x ∈ Subgroup.normalClosure (Q : Set G); rw [hgen]; trivial⟩
      exact ⟨a, hx, rfl⟩
  have h := (normal_hull_strong_embedding_of_corefree_point_embedding
    Q htight hodd hnormal hrank z hzQ hz hM hcore).map_mulEquiv e
  rwa [hmap] at h

theorem normal_hull_strong_embedding_of_odd_quotient_point_embedding
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hM :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (CFSG.oddCore J)
      CFSG.BenderSuzuki.IsStronglyEmbedded
        ((Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ CFSG.oddCore J))).subgroupOf
          (involutionPointHull (q zJ)))) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf
        (Subgroup.normalClosure (Q : Set G))) := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (CFSG.oddCore J)
  let R := (Q.subgroupOf J).map q
  let y := q zJ
  have hytwo : orderOf y = 2 := by
    have hzJ : orderOf zJ = 2 := (Subgroup.orderOf_coe zJ).symm.trans hz
    have hzI : IsInvolution zJ :=
      ⟨(orderOf_eq_prime_iff.mp hzJ).2, (orderOf_eq_prime_iff.mp hzJ).1⟩
    have hyI := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel
      q (normal_hull_odd_quotient_ker_odd Q) hzI
    exact orderOf_eq_prime_iff.mpr ⟨hyI.sq_eq_one, hyI.ne_one⟩
  have hyR : y ∈ R := Subgroup.mem_map.mpr ⟨zJ, hzQ, rfl⟩
  have htightR : TightlyEmbedded R :=
    normal_hull_odd_quotient_Q_tightly_embedded Q htight hodd hrank
  have hoddR : OddNormalizerOverlaps R :=
    normal_hull_odd_quotient_Q_odd_normalizer_overlaps Q htight hodd hrank
  have hnormalR : ¬ R.Normal :=
    normal_hull_odd_quotient_Q_nonnormal Q htight hodd hrank hnormal
  have hrankR : 2 ≤ twoRank R := hrank.trans (normal_hull_odd_quotient_Q_twoRank_le Q)
  have hcoreY : CFSG.oddCore (involutionPointHull y) = ⊥ :=
    normal_hull_odd_quotient_point_hull_corefree Q z hzQ
  have hgenR : Subgroup.normalClosure (R : Set (J ⧸ CFSG.oddCore J)) = ⊤ :=
    normal_hull_odd_quotient_Q_normalClosure_top Q hodd hnormal z hzQ hz
  have himage := strong_embedding_of_corefree_point_embedding_of_normal_generation
    R htightR hoddR hnormalR hrankR y hyR hytwo hM hcoreY hgenR
  exact normal_hull_strong_embedding_of_odd_core_quotient Q htight hodd hrank himage

theorem normal_hull_strong_embedding_of_odd_quotient_point_split
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    {A B : Type*} [Group A] [IsMulCommutative A] [Group B] [Finite B]
    (e :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (CFSG.oddCore J)
      involutionPointHull (q zJ) ≃* A × B)
    (M : Subgroup B) (hM : fusionStronglyEmbedded M)
    (hmember :
      let J := Subgroup.normalClosure (Q : Set G)
      let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
      let q := QuotientGroup.mk' (CFSG.oddCore J)
      ∀ x : involutionPointHull (q zJ),
        (e x).2 ∈ M ↔ (x : J ⧸ CFSG.oddCore J) ∈
          Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ CFSG.oddCore J))) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf
        (Subgroup.normalClosure (Q : Set G))) := by
  have hpoint := normal_hull_odd_quotient_point_hull_strong_embedding_of_split
    Q htight hodd hnormal hrank z hzQ hz e M hM hmember
  exact normal_hull_strong_embedding_of_odd_quotient_point_embedding
    Q htight hodd hnormal hrank z hzQ hz (native_strong_embedding_of_order_conditions hpoint)

end CFSG.ComponentClassification.AschbacherTightEmbedding
