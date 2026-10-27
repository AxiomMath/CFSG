module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem zpowers_involution_eq_one_or_self {A : Type} [CommGroup A] {a : A} (ha : a * a = 1) :
    ∀ y ∈ zpowers a, y = 1 ∨ y = a := by
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, zpow_two, ha, one_zpow]
  · right
    rw [hm, zpow_add, zpow_one, zpow_mul, zpow_two, ha, one_zpow, one_mul]

theorem exists_finset_closure_le {A : Type} [CommGroup A] (hA : ∀ a : A, a * a = 1)
    (Y : Finset A) :
    ∃ S : Finset A, S.card ≤ 2 ^ Y.card ∧ ∀ x ∈ closure (Y : Set A), x ∈ S := by
  classical
  induction Y using Finset.induction_on with
  | empty =>
    refine ⟨{1}, by simp, fun x hx => ?_⟩
    rw [Finset.coe_empty, closure_empty, mem_bot] at hx
    simp [hx]
  | insert a Y ha ih =>
    obtain ⟨S, hS, hSY⟩ := ih
    refine ⟨S ∪ S.image (· * a), ?_, ?_⟩
    · calc (S ∪ S.image (· * a)).card ≤ S.card + (S.image (· * a)).card :=
            Finset.card_union_le _ _
        _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
        _ = 2 * S.card := by ring
        _ ≤ 2 * 2 ^ Y.card := Nat.mul_le_mul_left 2 hS
        _ = 2 ^ (insert a Y).card := by
          rw [Finset.card_insert_of_notMem ha, pow_succ]
          ring
    · intro x hx
      rw [Finset.coe_insert, Set.insert_eq, closure_union, ← zpowers_eq_closure] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hx
      rcases zpowers_involution_eq_one_or_self (hA a) y hy with h | h
      · rw [h, one_mul]
        exact Finset.mem_union_left _ (hSY z hz)
      · rw [h]
        exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨z, hSY z hz, mul_comm z a⟩)

end CFSG.EvenSporadicStandard.Fin76b
