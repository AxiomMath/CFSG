module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard

open Equiv Equiv.Perm Subgroup

@[expose] def pairA : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def pairB : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def kleinFive : Subgroup (Perm (Fin 5)) where
  carrier := {1, pairA, pairB, pairA * pairB}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem mem_kleinFive_iff {x : Perm (Fin 5)} :
    x ∈ kleinFive ↔ x = 1 ∨ x = pairA ∨ x = pairB ∨ x = pairA * pairB := Iff.rfl

theorem pairA_mem_kleinFive : pairA ∈ kleinFive := mem_kleinFive_iff.2 (Or.inr (Or.inl rfl))

theorem pairB_mem_kleinFive : pairB ∈ kleinFive :=
  mem_kleinFive_iff.2 (Or.inr (Or.inr (Or.inl rfl)))

theorem card_kleinFive : Nat.card kleinFive = 4 := by
  have h : Nat.card kleinFive = Set.ncard ({1, pairA, pairB, pairA * pairB} : Set (Perm (Fin 5))) :=
    by rw [← Nat.card_coe_set_eq]; rfl
  rw [h, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
  all_goals decide

theorem sign_eq_one_of_mem_kleinFive {x : Perm (Fin 5)} (hx : x ∈ kleinFive) : Perm.sign x = 1 := by
  rcases mem_kleinFive_iff.1 hx with rfl | rfl | rfl | rfl <;> decide

theorem kleinFive_le_alternatingGroup : kleinFive ≤ alternatingGroup (Fin 5) := fun _ hx =>
  Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_mem_kleinFive hx)

theorem mul_self_eq_one_of_mem_kleinFive {x : Perm (Fin 5)} (hx : x ∈ kleinFive) : x * x = 1 := by
  rcases mem_kleinFive_iff.1 hx with rfl | rfl | rfl | rfl <;> decide

theorem mul_comm_of_mem_kleinFive {x y : Perm (Fin 5)} (hx : x ∈ kleinFive)
    (hy : y ∈ kleinFive) : x * y = y * x := by
  rcases mem_kleinFive_iff.1 hx with rfl | rfl | rfl | rfl <;>
    rcases mem_kleinFive_iff.1 hy with rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 100000 in
theorem mem_kleinFive_of_commute {σ : Perm (Fin 5)} (ha : σ * pairA = pairA * σ)
    (hb : σ * pairB = pairB * σ) : σ ∈ kleinFive := by
  have key : ∀ σ : Perm (Fin 5), σ * pairA = pairA * σ → σ * pairB = pairB * σ →
      σ = 1 ∨ σ = pairA ∨ σ = pairB ∨ σ = pairA * pairB := by
    decide
  exact mem_kleinFive_iff.2 (key σ ha hb)

end CFSG.OddStandard
