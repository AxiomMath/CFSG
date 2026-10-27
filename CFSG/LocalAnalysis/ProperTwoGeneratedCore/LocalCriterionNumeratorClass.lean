module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorLocal

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G] [Finite G]

theorem strong_embedding_full_involution_class (B : Subgroup G)
    (hB : fusionStronglyEmbedded B) (z : G) (hz : orderOf z = 2) :
    involutionPointClass z = {x : G | orderOf x = 2} := by
  ext x
  constructor
  · exact order_two_of_mem_pointClass hz
  · intro hx
    have hzI : IsInvolution z :=
      ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
    have hxI : IsInvolution x :=
      ⟨(orderOf_eq_prime_iff.mp hx).2, (orderOf_eq_prime_iff.mp hx).1⟩
    exact (native_strong_embedding_of_order_conditions hB).involutions_conjugate hzI hxI

theorem original_local_hull_internal_class
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z)
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u))) :
    let L := localInvolutionPointHull z u
    let zL : L := ⟨z, distinguished_mem_localInvolutionPointHull huz⟩
    involutionPointClass zL = {x : L | orderOf x = 2} ∧
      (Subtype.val '' involutionPointClass zL : Set G) =
        involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∧
      {x : G | x ∈ L ∧ orderOf x = 2} =
        involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) := by
  let L := localInvolutionPointHull z u
  let zL : L := ⟨z, distinguished_mem_localInvolutionPointHull huz⟩
  have hzL : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans h.distinguished_order
  have hclass : involutionPointClass zL = {x : L | orderOf x = 2} :=
    strong_embedding_full_involution_class (H.subgroupOf L) hP zL hzL
  have hmap : (Subtype.val '' involutionPointClass zL : Set G) =
      involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨g, hg⟩, rfl⟩
      refine ⟨⟨(g : G), ?_⟩, localInvolutionPointHull_le_centralizer z u y.property⟩
      exact congrArg Subtype.val hg
    · intro hx
      have hxL : x ∈ L := Subgroup.subset_closure hx
      let xL : L := ⟨x, hxL⟩
      have hxorder : orderOf xL = 2 :=
        (Subgroup.orderOf_coe xL).symm.trans
          (order_two_of_mem_pointClass h.distinguished_order hx.1)
      exact ⟨xL, hclass.symm ▸ hxorder, rfl⟩
  refine ⟨hclass, hmap, ?_⟩
  ext x
  constructor
  · rintro ⟨hxL, hxorder⟩
    let xL : L := ⟨x, hxL⟩
    have hxI : xL ∈ involutionPointClass zL :=
      hclass.symm ▸ (Subgroup.orderOf_coe xL).symm.trans hxorder
    exact hmap ▸ (show x ∈ (Subtype.val '' involutionPointClass zL : Set G) from
      ⟨xL, hxI, rfl⟩)
  · intro hx
    exact ⟨Subgroup.subset_closure hx,
      order_two_of_mem_pointClass h.distinguished_order hx.1⟩

theorem original_pair_full_local_involution_class
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2) (huz : Commute u z) (hut : Commute u t)
    (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b) :
    let L := localInvolutionPointHull z u
    let zL : L := ⟨z, distinguished_mem_localInvolutionPointHull huz⟩
    involutionPointClass zL = {x : L | orderOf x = 2} ∧
      (Subtype.val '' involutionPointClass zL : Set G) =
        involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∧
      {x : G | x ∈ L ∧ orderOf x = 2} =
        involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) := by
  obtain ⟨_, _, _, _, hP⟩ :=
    original_pair_local_hull_inputs h b hb u t hu huz hut htclass hflip
  exact original_local_hull_internal_class h u huz hP

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
