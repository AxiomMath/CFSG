module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Equiv Equiv.Perm Subgroup

structure SylData (T : Subgroup (Perm (Fin 11))) : Prop where
  even : ∀ t ∈ T, sign t = 1
  card : Nat.card ↥T = 2 ^ 7
  fix10 : ∀ t ∈ T, t 10 = 10
  stab8 : ∀ t ∈ T, ∀ x : Fin 11, (t x).val < 8 ↔ x.val < 8
  trans8 : ∀ x y : Fin 11, x.val < 8 → y.val < 8 → ∃ t ∈ T, t x = y
  swap89 : ∃ t ∈ T, t 8 = 9

@[expose] def c3 : Perm (Fin 11) := swap 8 9 * swap 9 10

theorem c3_pow_three : c3 ^ 3 = 1 := by decide

theorem c3_ne_one : c3 ≠ 1 := by decide

theorem orderOf_c3 : orderOf c3 = 3 := orderOf_eq_prime c3_pow_three c3_ne_one

theorem card_zpowers_c3 : Nat.card (zpowers c3) = 3 := by rw [Nat.card_zpowers, orderOf_c3]

@[expose] def FixDichotomy (T : Subgroup (Perm (Fin 11))) : Prop :=
  ∀ V : Subgroup (Perm (Fin 11)), IsPGroup 3 ↥V → V ≠ ⊥ →
    T ≤ normalizer (V : Set (Perm (Fin 11))) →
    (∀ x : Fin 11, (∀ v ∈ V, v x = x) ↔ x.val < 8) ∨
      (∀ x : Fin 11, (∀ v ∈ V, v x = x) ↔ x = 8 ∨ x = 9)

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
