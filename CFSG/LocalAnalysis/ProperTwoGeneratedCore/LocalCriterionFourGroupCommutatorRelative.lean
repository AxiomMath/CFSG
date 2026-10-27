module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorLift
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import Mathlib.GroupTheory.Index

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG

universe u v

variable {A : Type u} [Group A]
variable {I : Type v} [Group I] [MulDistribMulAction A I]

theorem invariant_actor_fixed_map (K : Subgroup I)
    [IsInvariant A I K] (a : A) :
    (actorFixedSubgroup (I := K) a).map K.subtype = K ⊓ actorFixedSubgroup a := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, congrArg Subtype.val hy⟩
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    exact Subtype.ext hx

theorem invariant_actor_fixed_card (K : Subgroup I)
    [IsInvariant A I K] (a : A) :
    Nat.card (actorFixedSubgroup (I := K) a) =
      Nat.card (K ⊓ actorFixedSubgroup (I := I) a : Subgroup I) := by
  rw [← invariant_actor_fixed_map K a]
  exact (Subgroup.card_map_of_injective K.subtype_injective).symm

theorem invariant_common_fixed_card (K : Subgroup I)
    [IsInvariant A I K] :
    Nat.card (fixedPointSubgroup A K) = Nat.card (K ⊓ fixedPointSubgroup A I : Subgroup I) := by
  rw [← fixedPointSubgroup_map_subtype_eq_inf K]
  exact (Subgroup.card_map_of_injective K.subtype_injective).symm

theorem four_group_invariant_subgroup_order_identity [Finite A] [Finite I]
    [IsKleinFour A] (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card I)) (K : Subgroup I) [IsInvariant A I K] :
    Nat.card K * Nat.card (K ⊓ fixedPointSubgroup A I : Subgroup I) ^ 2 =
      Nat.card (K ⊓ actorFixedSubgroup (I := I) a : Subgroup I) *
        Nat.card (K ⊓ actorFixedSubgroup (I := I) b : Subgroup I) *
          Nat.card (K ⊓ actorFixedSubgroup (I := I) (a * b) : Subgroup I) := by
  have hKodd : Odd (Nat.card K) := hodd.of_dvd_nat K.card_subgroup_dvd_card
  simpa only [invariant_actor_fixed_card, invariant_common_fixed_card] using
    four_group_order_identity (I := K) a b ha hb hab hKodd

theorem four_group_relative_index_identity [Finite A] [Finite I] [IsKleinFour A]
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card I)) (K : Subgroup I) [IsInvariant A I K] :
    K.index * (K.relIndex (fixedPointSubgroup A I)) ^ 2 =
      K.relIndex (actorFixedSubgroup (I := I) a) *
        K.relIndex (actorFixedSubgroup (I := I) b) *
          K.relIndex (actorFixedSubgroup (I := I) (a * b)) := by
  let E := fixedPointSubgroup A I
  let Ca := actorFixedSubgroup (I := I) a
  let Cb := actorFixedSubgroup (I := I) b
  let Cab := actorFixedSubgroup (I := I) (a * b)
  have hI := four_group_order_identity (I := I) a b ha hb hab hodd
  have hK := four_group_invariant_subgroup_order_identity a b ha hb hab hodd K
  change Nat.card I * Nat.card E ^ 2 = Nat.card Ca * Nat.card Cb * Nat.card Cab at hI
  change Nat.card K * Nat.card (K ⊓ E : Subgroup I) ^ 2 =
    Nat.card (K ⊓ Ca : Subgroup I) * Nat.card (K ⊓ Cb : Subgroup I) * Nat.card (K ⊓ Cab : Subgroup I) at hK
  apply Nat.mul_right_cancel (m := Nat.card K * Nat.card (K ⊓ E : Subgroup I) ^ 2)
    (Nat.mul_pos Nat.card_pos (pow_pos Nat.card_pos 2))
  calc
    _ = (K.index * Nat.card K) * (K.relIndex E * Nat.card (K ⊓ E : Subgroup I)) ^ 2 := by ring
    _ = Nat.card I * Nat.card E ^ 2 := by rw [K.index_mul_card, K.relIndex_mul_card E]
    _ = Nat.card Ca * Nat.card Cb * Nat.card Cab := hI
    _ = (K.relIndex Ca * Nat.card (K ⊓ Ca : Subgroup I)) *
        (K.relIndex Cb * Nat.card (K ⊓ Cb : Subgroup I)) *
          (K.relIndex Cab * Nat.card (K ⊓ Cab : Subgroup I)) := by
      rw [K.relIndex_mul_card Ca, K.relIndex_mul_card Cb, K.relIndex_mul_card Cab]
    _ = (K.relIndex Ca * K.relIndex Cb * K.relIndex Cab) *
        (Nat.card (K ⊓ Ca : Subgroup I) * Nat.card (K ⊓ Cb : Subgroup I) * Nat.card (K ⊓ Cab : Subgroup I)) := by ring
    _ = _ := by rw [← hK]

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
