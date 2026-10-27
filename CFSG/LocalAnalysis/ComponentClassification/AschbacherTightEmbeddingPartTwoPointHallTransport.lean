module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPointHall
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoHullQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoIndexTransport

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

def intersectionPresentationEquiv (H L : Subgroup G) :
    H.subgroupOf L ≃* L.subgroupOf H where
  toFun x := ⟨⟨(x.val : G), x.property⟩, x.val.property⟩
  invFun x := ⟨⟨(x.val : G), x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem hall_subgroup_map_mulEquiv {F K : Type*} [Group F] [Group K]
    (e : F ≃* K) (π : Set Nat.Primes) (D : Subgroup F)
    (hD : CFSG.IsHallSubgroup π D) :
    CFSG.IsHallSubgroup π (D.map e.toMonoidHom) := by
  have hcard : Nat.card (D.map e.toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective e.injective
  have hindex : (D.map e.toMonoidHom).index = D.index :=
    Subgroup.index_map_equiv (H := D) e
  refine ⟨?_, ?_⟩
  · intro p hp
    exact hD.p_in_pi_of_p_dvd_card p (hcard ▸ hp)
  · intro p hp
    exact hD.p_in_pi_of_p_dvd_index p (hindex ▸ hp)

theorem intersection_presentation_subgroup_ambient_image
    (H L : Subgroup G) (D : Subgroup (H.subgroupOf L)) :
    (D.map (H.subgroupOf L).subtype).map L.subtype =
      ((D.map (intersectionPresentationEquiv H L).toMonoidHom).map
        (L.subgroupOf H).subtype).map H.subtype := by
  simp only [Subgroup.map_map]
  congr 1

theorem intersection_presentation_normalizer_disjointness
    (H L : Subgroup G) (C : Subgroup L) (D : Subgroup (H.subgroupOf L))
    (hdisjoint : Disjoint C
      (Subgroup.normalizer (D.map (H.subgroupOf L).subtype : Set L))) :
    Disjoint ((C.map L.subtype).subgroupOf H)
      (Subgroup.normalizer ((D.map (intersectionPresentationEquiv H L).toMonoidHom).map
        (L.subgroupOf H).subtype : Set H)) := by
  have hambient := subgroup_image_disjoint_normalizer_of_internal_disjointness
    L C (D.map (H.subgroupOf L).subtype) hdisjoint
  have himage := intersection_presentation_subgroup_ambient_image H L D
  apply Subgroup.disjoint_def.mpr
  intro x hxC hxN
  have hxNG : (x : G) ∈ Subgroup.normalizer
      (((D.map (intersectionPresentationEquiv H L).toMonoidHom).map
        (L.subgroupOf H).subtype).map H.subtype : Set G) :=
    Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩)
  rw [← himage] at hxNG
  exact Subtype.ext (Subgroup.disjoint_def.mp hambient hxC hxNG)

variable [Finite G]

theorem involution_of_Q_mem_point_hull (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (x : G) (hxQ : x ∈ Q) (hx : orderOf x = 2) :
    x ∈ involutionPointHull z := by
  apply Subgroup.subset_closure
  rw [← conjugateQInvolutions_eq_pointClass Q hodd hnormal z hzQ hz]
  exact involution_mem_conjugateQInvolutions Q x hxQ hx

theorem normal_hull_point_hull_odd_index_of_corefree_point_strong_embedding
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (hrank : 2 ≤ twoRank Q) (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (hM : CFSG.BenderSuzuki.IsStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (involutionPointHull z)))
    (hcore : CFSG.oddCore (involutionPointHull z) = ⊥) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    Odd (involutionPointHull zJ).index := by
  let H := Subgroup.normalizer (Q : Set G)
  let L := involutionPointHull z
  let M := H.subgroupOf L
  let A := L.subgroupOf H
  let e := intersectionPresentationEquiv H L
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  have hzL : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hz
  have hzM : zL ∈ M := Subgroup.le_normalizer hzQ
  obtain ⟨w, hwQ, hw, hzw, _hcomm⟩ :=
    involution_has_commuting_companion_of_rank_two_Q Q hodd hnormal hrank z hzQ hz
  let wL : L := ⟨w, involution_of_Q_mem_point_hull Q hodd hnormal z hzQ hz w hwQ hw⟩
  have hwL : orderOf wL = 2 := (Subgroup.orderOf_coe wL).symm.trans hw
  have hwM : wL ∈ M := Subgroup.le_normalizer hwQ
  have hzwL : zL ≠ wL := fun heq => hzw (congrArg Subtype.val heq)
  have hLrank : 2 ≤ twoRank L := hrank.trans
    (Q_twoRank_le_point_hull Q hodd hnormal z hzQ hz)
  obtain ⟨E, hE, hEcard⟩ := CFSG.ComponentClassification.Helpers.twoRank_witness L
  have hcard : 4 ≤ Nat.card E := by
    rw [hEcard]
    exact (by norm_num : 4 = (2 : ℕ) ^ 2) ▸
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hLrank
  have hnative : TwoRankAtLeastTwo L :=
    (twoRankAtLeastTwo_of_elementary_card_ge_four E hE hcard).map_of_injective
      E.subtype E.subtype_injective
  have hgen : involutionCore L = ⊤ :=
    involution_core_eq_top_of_involution_normal_generation zL hzL
      (internal_hull_normalClosure_top Q hodd hnormal z hzQ hz)
  obtain ⟨_hmodel, hsolv, P, D, _hP, _hcompl, _hDodd, hHall,
      _hnormalizer, hcontainL, hdisjointL⟩ :=
    corefree_strong_embedding_root_hall_center_data M hM hnative hgen hcore
      zL wL hzM hwM hzL hwL hzwL
  let R := (P : Subgroup M).map M.subtype
  let C := (Subgroup.center R).map R.subtype
  let D' := D.map e.toMonoidHom
  let C' := (C.map L.subtype).subgroupOf H
  have hsolvA : Group.IsSolvable A := by
    let : Group.IsSolvable M := hsolv
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hHallA : CFSG.IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} D' :=
    hall_subgroup_map_mulEquiv e _ D hHall
  have hcontain : ∀ x : H, x ∈ Q.subgroupOf H → orderOf x = 2 → x ∈ C' := by
    intro x hxQ hx
    have hxG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    let xL : L := ⟨x, involution_of_Q_mem_point_hull Q hodd hnormal z hzQ hz x hxQ hxG⟩
    have hxM : xL ∈ M := x.property
    have hxL : orderOf xL = 2 := (Subgroup.orderOf_coe xL).symm.trans hxG
    exact Subgroup.mem_map.mpr ⟨xL, hcontainL xL hxM hxL, rfl⟩
  have hdisjoint : Disjoint C'
      (Subgroup.normalizer (D'.map A.subtype : Set H)) :=
    intersection_presentation_normalizer_disjointness H L C D hdisjointL
  exact normal_hull_point_hull_odd_index_of_hall_kernel_data Q hodd hnormal z hzQ hz
    hsolvA {p : Nat.Primes | p.val ≠ 2} D' hHallA C' hcontain hdisjoint

end CFSG.ComponentClassification.AschbacherTightEmbedding
