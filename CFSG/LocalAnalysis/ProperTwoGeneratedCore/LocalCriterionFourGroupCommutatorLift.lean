module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorOrder
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG

universe u v

variable {A : Type u} [Group A]
variable {I : Type v} [Group I] [MulDistribMulAction A I]

theorem lifted_actor_fixed_card (a : A) :
    Nat.card (actorFixedSubgroup (A := ULift.{v} A) (I := ULift.{u} I)
      (ULift.up a)) = Nat.card (actorFixedSubgroup (I := I) a) := by
  apply Nat.card_congr
  refine (Equiv.ulift : ULift.{u} I ≃ I).subtypeEquiv ?_
  intro x
  change (ULift.up (a • x.down) : ULift.{u} I) = x ↔ a • x.down = x.down
  exact ULift.ext_iff

theorem lifted_common_fixed_card :
    Nat.card (fixedPointSubgroup (ULift.{v} A) (ULift.{u} I)) =
      Nat.card (fixedPointSubgroup A I) := by
  apply Nat.card_congr
  refine (Equiv.ulift : ULift.{u} I ≃ I).subtypeEquiv ?_
  intro x
  change (∀ c : ULift.{v} A, c • x = x) ↔ ∀ a : A, a • x.down = x.down
  constructor
  · intro h a
    exact congrArg ULift.down (h (ULift.up a))
  · intro h c
    exact ULift.ext (h c.down)

theorem four_group_order_identity [Finite A] [Finite I] [IsKleinFour A]
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card I)) :
    Nat.card I * Nat.card (fixedPointSubgroup A I) ^ 2 =
      Nat.card (actorFixedSubgroup (I := I) a) *
        Nat.card (actorFixedSubgroup (I := I) b) *
          Nat.card (actorFixedSubgroup (I := I) (a * b)) := by
  let : IsKleinFour (ULift.{v} A) :=
    ⟨by simpa only [Nat.card_ulift] using (IsKleinFour.card_four (G := A)),
      (Monoid.exponent_eq_of_mulEquiv (MulEquiv.ulift : ULift.{v} A ≃* A)).trans
        IsKleinFour.exponent_two⟩
  have h := four_group_order_identity_same_universe
    (A := ULift.{v} A) (V := ULift.{u} I) (ULift.up a) (ULift.up b)
    (fun h => ha (congrArg ULift.down h))
    (fun h => hb (congrArg ULift.down h))
    (fun h => hab (congrArg ULift.down h))
    (by simpa only [Nat.card_ulift] using hodd)
  have habup : (ULift.up a : ULift.{v} A) * ULift.up b = ULift.up (a * b) := rfl
  rw [habup] at h
  simpa only [Nat.card_ulift, lifted_common_fixed_card, lifted_actor_fixed_card] using h

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
