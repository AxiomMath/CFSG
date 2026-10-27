module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairBasic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u v w

variable {G : Type u} [Group G] [Finite G]

theorem original_point_involution_intersection_card
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z)
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u))) :
    Nat.card {x : localInvolutionPointHull z u //
        x ∈ H.subgroupOf (localInvolutionPointHull z u) ∧ IsInvolution x} =
      Nat.card ↥(involutionPointClass z ∩
        (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)) := by
  let L := localInvolutionPointHull z u
  let S : Set G := involutionPointClass z ∩
    (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)
  have hclass := (original_local_hull_internal_class h u huz hP).2.2
  let f : {x : L // x ∈ H.subgroupOf L ∧ IsInvolution x} → S := fun x => by
    have hxorder : orderOf (x.val : G) = 2 := (Subgroup.orderOf_coe x.val).trans
      (orderOf_eq_prime_iff.mpr ⟨x.property.2.sq_eq_one, x.property.2.ne_one⟩)
    exact ⟨x.val, (Set.ext_iff.mp hclass (x.val : G)).mp ⟨x.val.property, hxorder⟩,
      x.property.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : S => (y : G)) hxy
    · intro y
      have hyL : (y : G) ∈ L := Subgroup.subset_closure y.property.1
      let yL : L := ⟨y, hyL⟩
      have hyorder : orderOf yL = 2 := (Subgroup.orderOf_coe yL).symm.trans
        (order_two_of_mem_pointClass h.distinguished_order y.property.1.1)
      have hyI : IsInvolution yL :=
        ⟨(orderOf_eq_prime_iff.mp hyorder).2, (orderOf_eq_prime_iff.mp hyorder).1⟩
      exact ⟨⟨yL, y.property.2, hyI⟩, Subtype.ext rfl⟩
  exact Nat.card_congr (Equiv.ofBijective f hf)

theorem original_point_parameter_of_stabilizer_map
    {F : Type v} [Group F]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (u : G) (huz : Commute u z)
    (hP : fusionStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)))
    (E : localInvolutionPointHull z u ≃* F) (B : Subgroup F)
    (hPB : (H.subgroupOf (localInvolutionPointHull z u)).map E.toMonoidHom = B)
    (q : ℕ) (hq : 1 ≤ q)
    (hcount : Nat.card {x : F // x ∈ B ∧ IsInvolution x} = q - 1) :
    q = Nat.card ↥(({1} : Set G) ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G))) := by
  classical
  let L := localInvolutionPointHull z u
  let S : Set G := involutionPointClass z ∩
    (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)
  have hPcomap : H.subgroupOf L = B.comap E.toMonoidHom := by
    rw [← hPB, Subgroup.comap_map_eq_self_of_injective E.injective]
  have hS : Nat.card S = q - 1 := by
    rw [← original_point_involution_intersection_card h u huz hP, hPcomap]
    exact (point_involution_card_comap E B).trans hcount
  have hone : (1 : G) ∉ S := by
    intro h1
    have horder := order_two_of_mem_pointClass h.distinguished_order h1.1.1
    rw [orderOf_one] at horder
    omega
  have hcard : Nat.card ↥(({1} : Set G) ∪ S) = Nat.card S + 1 := by
    rw [Set.singleton_union, Nat.card_congr (Equiv.Set.insert hone), Nat.card_sum]
    rw [Nat.card_unique (α := PUnit.{u + 1})]
  rw [hcard, hS]
  omega

theorem original_local_point_parameter_of_abstract_model
    {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2) (huz : Commute u z) (hut : Commute u t)
    (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    (e : localInvolutionPointHull z u ≃* F) (hrank : TwoRankAtLeastTwo F)
    (htrans : MulAction.IsPretransitive F Ξ) (a₀ : Ξ)
    (hB : fusionStronglyEmbedded (MulAction.stabilizer F a₀))
    (q : ℕ) (hq : 1 ≤ q)
    (hcount : Nat.card {x : F // x ∈ MulAction.stabilizer F a₀ ∧ IsInvolution x} =
      q - 1) :
    q = Nat.card ↥(({1} : Set G) ∪
      (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
        (H : Set G))) := by
  obtain ⟨_, _, _, _, hP⟩ :=
    original_pair_local_hull_inputs h b hb u t hu huz hut htclass hflip
  have hPbase : fusionStronglyEmbedded
      ((rightCosetStabilizer H (rightCosetMk H 1)).subgroupOf
        (localInvolutionPointHull z u)) := by
    rw [rightCosetStabilizer_base]
    exact hP
  obtain ⟨E, _, hE, _, _⟩ := original_right_orbit_model_identification H
    (localInvolutionPointHull z u) (rightCosetMk H 1) hPbase hrank htrans a₀ hB e
  rw [rightCosetStabilizer_base] at hE
  exact original_point_parameter_of_stabilizer_map h u huz hP E
    (MulAction.stabilizer F a₀) hE q hq hcount

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
