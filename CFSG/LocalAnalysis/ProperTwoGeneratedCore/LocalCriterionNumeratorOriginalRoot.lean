module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorClass

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem original_point_involution_set_image
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z)
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u))) :
    let L := localInvolutionPointHull z u
    L.subtype '' {x : L | x ∈ H.subgroupOf L ∧ IsInvolution x} =
      involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G) := by
  let L := localInvolutionPointHull z u
  have hclass := (original_local_hull_internal_class h u huz hP).2.2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyorder : orderOf (y : G) = 2 := (Subgroup.orderOf_coe y).trans
      (orderOf_eq_prime_iff.mpr ⟨hy.2.sq_eq_one, hy.2.ne_one⟩)
    exact ⟨(Set.ext_iff.mp hclass (y : G)).mp ⟨y.property, hyorder⟩, hy.1⟩
  · intro hx
    have hxL : x ∈ L := Subgroup.subset_closure hx.1
    let xL : L := ⟨x, hxL⟩
    have hxorder : orderOf xL = 2 := (Subgroup.orderOf_coe xL).symm.trans
      (order_two_of_mem_pointClass h.distinguished_order hx.1.1)
    exact ⟨xL, ⟨hx.2, (orderOf_eq_prime_iff.mp hxorder).2,
      (orderOf_eq_prime_iff.mp hxorder).1⟩, rfl⟩

theorem original_whole_point_root_of_central_odd_surjection
    {F : Type v} [Group F]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z)
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)))
    (f : localInvolutionPointHull z u →* F) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center (localInvolutionPointHull z u))
    (B U : Subgroup F)
    (hPB : (H.subgroupOf (localInvolutionPointHull z u)).map f = B)
    (hU : IsElementaryAbelian 2 U)
    (hUset : (U : Set F) = {1} ∪ {x : F | x ∈ B ∧ IsInvolution x}) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧
      A ≤ H ⊓ localInvolutionPointHull z u ∧
      (A : Set G) = {1} ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G)) ∧
      Nat.card A = Nat.card U := by
  let L := localInvolutionPointHull z u
  let P := H.subgroupOf L
  let s : Set L := {x : L | x ∈ P ∧ IsInvolution x}
  let V := Subgroup.closure s
  obtain ⟨helem, hVP, _hmap, _hinj, hset, hcard⟩ :=
    whole_point_involution_root_of_central_odd_surjection f hf hodd hcentral
      P B U hPB hU hUset
  let : IsElementaryAbelian 2 V := helem
  let A := V.map L.subtype
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  have hAle : A ≤ H ⊓ L := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨hVP hy, y.property⟩
  have hAset : (A : Set G) = {1} ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G)) := by
    change L.subtype '' (V : Set L) = _
    rw [hset, Set.image_union, Set.image_singleton]
    rw [original_point_involution_set_image h u huz hP]
    rfl
  have hAcard : Nat.card A = Nat.card U :=
    (Subgroup.card_map_of_injective L.subtype_injective).trans hcard
  exact ⟨A, hAelem, hAle, hAset, hAcard⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
