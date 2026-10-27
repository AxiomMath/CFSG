module

public import CFSG.GroupTheory.FourGroupOddOrderIdentitySupport

public section

namespace CFSG.GroupTheory

universe u v

theorem odd_group_four_group_centralizer_order_identity {A : Type u} {X : Type v} [Group A]
    [IsKleinFour A] [Fintype A] [DecidableEq A] [Group X] [Finite X] [MulDistribMulAction A X]
    (hX : Odd (Nat.card X)) :
    Nat.card X * Nat.card (fixedPointSubgroup A X) ^ 2 =
        ∏ a ∈ Finset.univ.erase (1 : A), Nat.card (fixedPointSubgroup (Subgroup.zpowers a) X) ∧
      ∀ Y : Subgroup X, (∀ a : A, ∀ y ∈ Y, a • y ∈ Y) →
        Y.index * Y.relIndex (fixedPointSubgroup A X) ^ 2 =
          ∏ a ∈ Finset.univ.erase (1 : A),
            Y.relIndex (fixedPointSubgroup (Subgroup.zpowers a) X) := by
  have habs : ∀ (Z : Type v) [Group Z] [Finite Z] [MulDistribMulAction A Z],
      Odd (Nat.card Z) → Nat.card Z * Nat.card (fixedPointSubgroup A Z) ^ 2 =
        ∏ a ∈ Finset.univ.erase (1 : A),
          Nat.card (fixedPointSubgroup (Subgroup.zpowers a) Z) := by
    intro Z _ _ _ hZ
    have : IsKleinFour (ULift.{v} A) :=
      ⟨by rw [Nat.card_ulift]; exact IsKleinFour.card_four,
        (Monoid.exponent_eq_of_mulEquiv MulEquiv.ulift).trans IsKleinFour.exponent_two⟩
    have hZ' : Odd (Nat.card (ULift.{u} Z)) := by rwa [Nat.card_ulift]
    have h := card_mul_card_fixedPointSubgroup_sq_of_universe (A := ULift.{v} A)
      (X := ULift.{u} Z) hZ'
    rw [Nat.card_ulift, card_fixedPointSubgroup_ulift] at h
    rw [h]
    refine Finset.prod_nbij' ULift.down ULift.up ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_
    · intro a ha
      rw [Finset.mem_erase] at ha ⊢
      exact ⟨fun h1 => ha.1 (congrArg ULift.up h1), Finset.mem_univ _⟩
    · intro a ha
      rw [Finset.mem_erase] at ha ⊢
      exact ⟨fun h1 => ha.1 (congrArg ULift.down h1), Finset.mem_univ _⟩
    · intro a _
      exact card_fixedPointSubgroup_zpowers_ulift (X := Z) a.down
  refine ⟨habs X hX, fun Y hY => ?_⟩
  have : CFSG.IsInvariant A X Y :=
    ⟨fun a g => ⟨hY a g, fun h => by simpa using hY a⁻¹ _ h⟩⟩
  have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hX (Subgroup.card_subgroup_dvd_card Y)
  have hYabs := habs Y hYodd
  rw [card_fixedPointSubgroup_subtype Y (fun b y => rfl),
    Finset.prod_congr rfl fun a _ =>
      card_fixedPointSubgroup_subtype (B := Subgroup.zpowers a) Y (fun b y => rfl)] at hYabs
  have hpos : 0 < Nat.card Y * Nat.card (Y ⊓ fixedPointSubgroup A X : Subgroup X) ^ 2 :=
    Nat.mul_pos Nat.card_pos (pow_pos Nat.card_pos 2)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Y.index * Y.relIndex (fixedPointSubgroup A X) ^ 2 *
        (Nat.card Y * Nat.card (Y ⊓ fixedPointSubgroup A X : Subgroup X) ^ 2)
      = (Nat.card Y * Y.index) * (Y.relIndex (fixedPointSubgroup A X) *
          Nat.card (Y ⊓ fixedPointSubgroup A X : Subgroup X)) ^ 2 := by ring
    _ = Nat.card X * Nat.card (fixedPointSubgroup A X) ^ 2 := by
      rw [Subgroup.card_mul_index, Subgroup.relIndex_mul_card]
    _ = ∏ a ∈ Finset.univ.erase (1 : A),
          Nat.card (fixedPointSubgroup (Subgroup.zpowers a) X) := habs X hX
    _ = ∏ a ∈ Finset.univ.erase (1 : A),
          (Y.relIndex (fixedPointSubgroup (Subgroup.zpowers a) X) *
            Nat.card (Y ⊓ fixedPointSubgroup (Subgroup.zpowers a) X : Subgroup X)) :=
      Finset.prod_congr rfl fun a _ => (Subgroup.relIndex_mul_card _ _).symm
    _ = (∏ a ∈ Finset.univ.erase (1 : A),
          Y.relIndex (fixedPointSubgroup (Subgroup.zpowers a) X)) *
        (Nat.card Y * Nat.card (Y ⊓ fixedPointSubgroup A X : Subgroup X) ^ 2) := by
      rw [Finset.prod_mul_distrib, hYabs]

end CFSG.GroupTheory
