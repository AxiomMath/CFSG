module
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Ring

variable {R : Type*} [Ring R]

def sqZeroUnit {x : R} (hx : x * x = 0) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by rw [add_mul, one_mul, mul_sub, mul_one, hx]; abel
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, hx]; abel

@[simp]
theorem sqZeroUnit_val {x : R} (hx : x * x = 0) : (sqZeroUnit hx : R) = 1 + x := (rfl)

@[simp]
theorem sqZeroUnit_inv_val {x : R} (hx : x * x = 0) :
    ((sqZeroUnit hx)⁻¹ : Rˣ).val = 1 - x := (rfl)

theorem isUnit_one_add_of_sq_eq_zero {x : R} (hx : x * x = 0) : IsUnit (1 + x) :=
  ⟨sqZeroUnit hx, rfl⟩

theorem commute_anticommutator_left {x y : R} (hx : x * x = 0) :
    Commute (x * y + y * x) x := by
  rw [commute_iff_eq]
  have h1 : (x * y + y * x) * x = x * y * x := by
    rw [add_mul, mul_assoc y x x, hx, mul_zero, add_zero]
  have h2 : x * (x * y + y * x) = x * y * x := by
    rw [mul_add, ← mul_assoc x x y, hx, zero_mul, zero_add, mul_assoc]
  exact h1.trans h2.symm

theorem commute_anticommutator_right {x y : R} (hy : y * y = 0) :
    Commute (x * y + y * x) y := by
  have h := commute_anticommutator_left (x := y) (y := x) hy
  rwa [add_comm (y * x)] at h

theorem commute_anticommutator_of_mem_closure {x y : R} (hx : x * x = 0) (hy : y * y = 0)
    {u : Rˣ} (hu : u ∈ Subgroup.closure {sqZeroUnit hx, sqZeroUnit hy}) :
    Commute (x * y + y * x) (u : R) := by
  induction hu using Subgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h <;> subst h <;> rw [sqZeroUnit_val]
      · exact (Commute.one_right _).add_right (commute_anticommutator_left hx)
      · exact (Commute.one_right _).add_right (commute_anticommutator_right hy)
  | one => rw [Units.val_one]; exact Commute.one_right _
  | mul a b _ _ ha hb => rw [Units.val_mul]; exact ha.mul_right hb
  | inv a _ ha => exact ha.units_inv_right

end Ring

section Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem commute_anticommutator_end_left (X Y : Module.End k V) (hX : X * X = 0) :
    Commute (X * Y + Y * X) X :=
  commute_anticommutator_left hX

theorem commute_anticommutator_end_right (X Y : Module.End k V) (hY : Y * Y = 0) :
    Commute (X * Y + Y * X) Y :=
  commute_anticommutator_right hY

theorem commute_anticommutator_end_of_mem_closure (X Y : Module.End k V)
    (hX : X * X = 0) (hY : Y * Y = 0) (g : LinearMap.GeneralLinearGroup k V)
    (hg : g ∈ Subgroup.closure {sqZeroUnit hX, sqZeroUnit hY}) :
    Commute (X * Y + Y * X) (g : Module.End k V) :=
  commute_anticommutator_of_mem_closure hX hY hg

end Module

end CFSG.FeitThompson
