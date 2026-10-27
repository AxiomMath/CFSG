module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ClassicalInvolution.Q3.AE

@[ext] structure Wr (n : ℕ) where
  vec : Fin n → ZMod 2
  perm : Equiv.Perm (Fin n)

namespace Wr

variable {n : ℕ}

instance : DecidableEq (Wr n) := fun a b =>
  decidable_of_iff (a.vec = b.vec ∧ a.perm = b.perm) (Wr.ext_iff (x := a) (y := b)).symm

instance : Mul (Wr n) := ⟨fun a b => ⟨fun i => a.vec i + b.vec (a.perm.symm i), a.perm * b.perm⟩⟩

instance : One (Wr n) := ⟨⟨0, 1⟩⟩

instance : Inv (Wr n) := ⟨fun a => ⟨fun i => a.vec (a.perm i), a.perm⁻¹⟩⟩

theorem mul_vec (a b : Wr n) (i : Fin n) : (a * b).vec i = a.vec i + b.vec (a.perm.symm i) := rfl

theorem mul_perm (a b : Wr n) : (a * b).perm = a.perm * b.perm := rfl

theorem one_vec : (1 : Wr n).vec = 0 := rfl

theorem one_perm : (1 : Wr n).perm = 1 := rfl

theorem inv_vec (a : Wr n) (i : Fin n) : (a⁻¹).vec i = a.vec (a.perm i) := rfl

theorem inv_perm (a : Wr n) : (a⁻¹).perm = a.perm⁻¹ := rfl

theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

instance : Group (Wr n) where
  mul_assoc a b c := by
    refine Wr.ext (funext fun i => ?_) ?_
    · simp only [mul_vec, mul_perm, Equiv.Perm.mul_def, Equiv.symm_trans_apply]
      ring
    · simp only [mul_perm, mul_assoc]
  one_mul a := by
    refine Wr.ext (funext fun i => ?_) ?_
    · simp only [mul_vec, one_vec, one_perm, Pi.zero_apply, zero_add]
      rfl
    · simp [mul_perm, one_perm]
  mul_one a := by
    refine Wr.ext (funext fun i => ?_) ?_
    · simp [mul_vec, one_vec]
    · simp [mul_perm, one_perm]
  inv_mul_cancel a := by
    refine Wr.ext (funext fun i => ?_) ?_
    · simp only [mul_vec, inv_vec, inv_perm, one_vec]
      simp [Equiv.Perm.inv_def, zmod_two_add_self]
    · simp [mul_perm, inv_perm, one_perm]

instance : Fintype (Wr n) :=
  Fintype.ofEquiv ((Fin n → ZMod 2) × Equiv.Perm (Fin n))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun a => (a.vec, a.perm)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[expose] def ofVec (v : Fin n → ZMod 2) : Wr n := ⟨v, 1⟩

@[expose] def ofPerm (σ : Equiv.Perm (Fin n)) : Wr n := ⟨0, σ⟩

@[expose] def wsum (a : Wr n) : ZMod 2 := ∑ i, a.vec i

@[expose] def allOnes (n : ℕ) : Wr n := ⟨fun _ => 1, 1⟩

theorem allOnes_comm (a : Wr n) : allOnes n * a = a * allOnes n := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (1 : ZMod 2) + a.vec ((1 : Equiv.Perm (Fin n)).symm i) = a.vec i + 1
    rw [add_comm]
    rfl
  · simp [mul_perm, allOnes]

end Wr

end CFSG.ClassicalInvolution.Q3.AE
