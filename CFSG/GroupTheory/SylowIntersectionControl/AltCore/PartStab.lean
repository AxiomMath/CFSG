module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.AltCore

open Equiv Equiv.Perm Subgroup

@[expose] def partStab {n : ℕ} (s : Setoid (Fin n)) : Subgroup (Perm (Fin n)) where
  carrier := {g | ∀ x y, s.r (g x) (g y) ↔ s.r x y}
  mul_mem' := by
    intro a b ha hb x y
    simp only [Set.mem_setOf_eq, Perm.mul_apply] at *
    rw [ha, hb]
  one_mem' := by intro x y; simp
  inv_mem' := by
    intro a ha x y
    simp only [Set.mem_setOf_eq] at *
    have := ha (a⁻¹ x) (a⁻¹ y)
    rw [show a (a⁻¹ x) = x from a.apply_symm_apply x,
      show a (a⁻¹ y) = y from a.apply_symm_apply y] at this
    exact this.symm

theorem mem_partStab_iff {n : ℕ} {s : Setoid (Fin n)} {g : Perm (Fin n)} :
    g ∈ partStab s ↔ ∀ x y, s.r (g x) (g y) ↔ s.r x y :=
  Iff.rfl

end CFSG.GroupTheory.AltCore
