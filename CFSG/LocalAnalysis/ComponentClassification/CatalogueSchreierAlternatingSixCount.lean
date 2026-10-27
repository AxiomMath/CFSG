module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixGenerators
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingImagePairs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

open Equiv
open Finset

@[expose] def FirstImage (a : alternatingGroup (Fin 6)) : Prop := a ^ 3 = 1 ∧ a ≠ 1

@[expose] def SecondImage (a b : alternatingGroup (Fin 6)) : Prop :=
  b ^ 5 = 1 ∧ b ≠ 1 ∧ (a * b) ^ 4 = 1 ∧ (a * b) ^ 2 ≠ 1 ∧
    (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1

instance firstImageDecidable : DecidablePred FirstImage := fun a =>
  inferInstanceAs (Decidable (a ^ 3 = 1 ∧ a ≠ 1))

instance secondImageDecidable (a : alternatingGroup (Fin 6)) : DecidablePred (SecondImage a) :=
  fun b => inferInstanceAs (Decidable
    (b ^ 5 = 1 ∧ b ≠ 1 ∧ (a * b) ^ 4 = 1 ∧ (a * b) ^ 2 ≠ 1 ∧
      (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 ∧ a * b * a⁻¹ * b⁻¹ ≠ 1))

theorem firstImage_iff_order (a : alternatingGroup (Fin 6)) :
    FirstImage a ↔ orderOf a = 3 :=
  orderOf_eq_prime_iff.symm

theorem secondImage_iff_orders (a b : alternatingGroup (Fin 6)) :
    SecondImage a b ↔ orderOf b = 5 ∧ orderOf (a * b) = 4 ∧
      orderOf (a * b * a⁻¹ * b⁻¹) = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · rintro ⟨hb5, hb1, hab4, hab2, hc2, hc1⟩
    exact ⟨orderOf_eq_prime hb5 hb1,
      orderOf_eq_prime_pow (p := 2) (n := 1) hab2 hab4, orderOf_eq_prime hc2 hc1⟩
  · rintro ⟨hb, hab, hc⟩
    have hb' := orderOf_eq_prime_iff.mp hb
    have hab4 : (a * b) ^ 4 = 1 := hab ▸ pow_orderOf_eq_one (a * b)
    have hab2 : (a * b) ^ 2 ≠ 1 := by
      intro hone
      have hd := orderOf_dvd_of_pow_eq_one hone
      rw [hab] at hd
      norm_num at hd
    have hc' := orderOf_eq_prime_iff.mp hc
    exact ⟨hb'.1, hb'.2, hab4, hab2, hc'.1, hc'.2⟩

private def doubleThreePermutation : Perm (Fin 6) :=
  xPermutation * swap 3 4 * swap 4 5

private theorem doubleThree_even : doubleThreePermutation.sign = 1 := by decide +kernel

private def doubleThree : alternatingGroup (Fin 6) :=
  ⟨doubleThreePermutation, Perm.mem_alternatingGroup.mpr doubleThree_even⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem firstImage_count :
    (univ.filter FirstImage).card = 80 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem singleThree_secondImage_count :
    (univ.filter (SecondImage x)).card = 18 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem doubleThree_secondImage_count :
    (univ.filter (SecondImage doubleThree)).card = 18 := by decide +kernel

private theorem representative_cycleTypes :
    xPermutation.cycleType = {3} ∧ doubleThreePermutation.cycleType = {3, 3} := by
  have hx : xPermutation.support.card = 3 := by decide +kernel
  have hz : doubleThreePermutation.support.card = 6 ∧ doubleThreePermutation ^ 3 = 1 := by
    decide +kernel
  refine ⟨card_support_eq_three_iff.mp hx, ?_⟩
  have htype := Perm.cycleType_of_pow_prime_eq_one hz.2
  have hsum := Perm.sum_cycleType doubleThreePermutation
  rw [htype, Multiset.sum_replicate, smul_eq_mul, hz.1] at hsum
  have hcard : doubleThreePermutation.cycleType.card = 2 := by omega
  simpa [hcard] using htype

private theorem firstImage_conjugate_representative (a : alternatingGroup (Fin 6))
    (ha : FirstImage a) :
    ∃ representative ∈ ({x, doubleThree} : Set (alternatingGroup (Fin 6))),
      ∃ permutation : Perm (Fin 6),
        MulAut.conjNormal (H := alternatingGroup (Fin 6)) permutation representative = a := by
  have horder : orderOf (a : Perm (Fin 6)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact (firstImage_iff_order a).mp ha
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (horder ▸ Nat.prime_three)
  have hsum := Perm.sum_cycleType_le (a : Perm (Fin 6))
  simp only [hk, horder, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hkcases : k = 0 ∨ k = 1 := by omega
  have hrepresentative : ∃ representative ∈ ({x, doubleThree} : Set (alternatingGroup (Fin 6))),
      (representative : Perm (Fin 6)).cycleType = (a : Perm (Fin 6)).cycleType := by
    rcases hkcases with rfl | rfl
    · refine ⟨x, by simp, ?_⟩
      exact representative_cycleTypes.1.trans (by simpa [horder] using hk.symm)
    · refine ⟨doubleThree, by simp, ?_⟩
      exact representative_cycleTypes.2.trans (by simpa [horder] using hk.symm)
  obtain ⟨representative, hrep, htype⟩ := hrepresentative
  obtain ⟨permutation, hpermutation⟩ :=
    isConj_iff.mp (Perm.isConj_of_cycleType_eq htype)
  refine ⟨representative, hrep, permutation, ?_⟩
  apply Subtype.ext
  exact (MulAut.conjNormal_apply permutation representative).trans hpermutation

private theorem secondImage_map_iff (automorphism : MulAut (alternatingGroup (Fin 6)))
    (a b : alternatingGroup (Fin 6)) :
    SecondImage (automorphism a) (automorphism b) ↔ SecondImage a b := by
  rw [secondImage_iff_orders, secondImage_iff_orders]
  simp only [← map_mul, ← map_inv, MulEquiv.orderOf_eq]

private theorem secondImage_card_conjugate (a : alternatingGroup (Fin 6))
    (automorphism : MulAut (alternatingGroup (Fin 6))) :
    Nat.card {b // SecondImage (automorphism a) b} = Nat.card {b // SecondImage a b} := by
  apply (Nat.card_congr (automorphism.toEquiv.subtypeEquiv
    (fun b => (secondImage_map_iff automorphism a b).symm))).symm

theorem secondImage_card (a : alternatingGroup (Fin 6)) (ha : FirstImage a) :
    Nat.card {b // SecondImage a b} = 18 := by
  obtain ⟨representative, hrep, permutation, hpermutation⟩ :=
    firstImage_conjugate_representative a ha
  rw [← hpermutation, secondImage_card_conjugate]
  rcases Set.mem_insert_iff.mp hrep with rfl | hrep
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact singleThree_secondImage_count
  · have heq := Set.mem_singleton_iff.mp hrep
    rw [heq, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact doubleThree_secondImage_count

private theorem imagePairOrders_iff (a b : alternatingGroup (Fin 6)) :
    (a, b) ∈ ImagePairOrders x y ↔ FirstImage a ∧ SecondImage a b := by
  rw [firstImage_iff_order, secondImage_iff_orders]
  simp only [ImagePairOrders, Set.mem_ofPred_eq, x_order, y_order, xy_order, commutator_order]

private noncomputable def candidatePairEquivalence :
    ImagePairOrders x y ≃ (a : {a // FirstImage a}) × {b // SecondImage a.val b} where
  toFun pair :=
    ⟨⟨pair.val.1, ((imagePairOrders_iff _ _).mp pair.property).1⟩,
      ⟨pair.val.2, ((imagePairOrders_iff _ _).mp pair.property).2⟩⟩
  invFun pair :=
    ⟨(pair.1.val, pair.2.val), (imagePairOrders_iff _ _).mpr ⟨pair.1.property, pair.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem image_pair_count : Nat.card (ImagePairOrders x y) = 1440 := by
  rw [Nat.card_congr candidatePairEquivalence, Nat.card_sigma]
  have hsum : (∑ a : {a // FirstImage a}, Nat.card {b // SecondImage a.val b}) =
      ∑ _a : {a // FirstImage a}, 18 := by
    apply Finset.sum_congr rfl
    intro a _
    exact secondImage_card a.val a.property
  rw [hsum]
  have hfirst : Fintype.card {a // FirstImage a} = 80 := by
    rw [Fintype.card_subtype]
    exact firstImage_count
  simp only [Finset.sum_const, Finset.card_univ, hfirst, nsmul_eq_mul]
  decide

theorem automorphism_card_le : Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ 1440 := by
  have hbound := automorphism_card_le_image_pairs x y generating_pair
  rwa [image_pair_count] at hbound

end CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
