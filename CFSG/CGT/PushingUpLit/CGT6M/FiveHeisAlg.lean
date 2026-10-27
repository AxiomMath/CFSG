module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open Matrix
open scoped commutatorElement

section Heis

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

structure HeisRel (A B C : Matrix n n K) (σ : K) : Prop where
  AA : A * A = 0
  BB : B * B = 0
  AB : A * B = σ • C
  BA : B * A = -(σ • C)
  CA : C * A = 0
  AC : A * C = 0
  CB : C * B = 0
  BC : B * C = 0
  CC : C * C = 0

@[expose] def Hm (A B C : Matrix n n K) (x y z : K) : Matrix n n K :=
  1 + x • A + y • B + z • C

variable {A B C : Matrix n n K} {σ : K}

theorem Hm_mul (h : HeisRel A B C σ) (x y z x' y' z' : K) :
    Hm A B C x y z * Hm A B C x' y' z' =
      Hm A B C (x + x') (y + y') (z + z' + σ * (x * y' - y * x')) := by
  simp only [Hm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, h.AA, h.BB, h.AB, h.BA, h.CA, h.AC, h.CB, h.BC, h.CC, smul_zero, smul_neg]
  module

omit [Fintype n] in
theorem Hm_zero : Hm A B C 0 0 0 = 1 := by simp [Hm]

theorem Hm_inv_right (h : HeisRel A B C σ) (x y z : K) :
    Hm A B C x y z * Hm A B C (-x) (-y) (-z) = 1 := by
  rw [Hm_mul h, ← Hm_zero (A := A) (B := B) (C := C)]
  congr 1 <;> ring

theorem Hm_inv_left (h : HeisRel A B C σ) (x y z : K) :
    Hm A B C (-x) (-y) (-z) * Hm A B C x y z = 1 := by
  rw [Hm_mul h, ← Hm_zero (A := A) (B := B) (C := C)]
  congr 1 <;> ring

@[expose] def Hu (h : HeisRel A B C σ) (x y z : K) : GL n K :=
  ⟨Hm A B C x y z, Hm A B C (-x) (-y) (-z), Hm_inv_right h x y z, Hm_inv_left h x y z⟩

theorem Hu_congr (h : HeisRel A B C σ) {x y z x' y' z' : K} (hx : x = x') (hy : y = y')
    (hz : z = z') : Hu h x y z = Hu h x' y' z' := by
  subst hx hy hz
  rfl

theorem Hu_mul (h : HeisRel A B C σ) (x y z x' y' z' : K) :
    Hu h x y z * Hu h x' y' z' = Hu h (x + x') (y + y') (z + z' + σ * (x * y' - y * x')) :=
  Units.ext (Hm_mul h x y z x' y' z')

theorem Hu_zero (h : HeisRel A B C σ) : Hu h 0 0 0 = 1 := Units.ext Hm_zero

theorem Hu_inv (h : HeisRel A B C σ) (x y z : K) :
    (Hu h x y z)⁻¹ = Hu h (-x) (-y) (-z) :=
  inv_eq_of_mul_eq_one_right (Units.ext (Hm_inv_right h x y z))

theorem Hu_x_pow (h : HeisRel A B C σ) (x : K) (k : ℕ) : (Hu h x 0 0) ^ k = Hu h (k * x) 0 0 := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact (Hu_zero h).symm
  | succ k ih =>
    rw [pow_succ, ih, Hu_mul]
    apply Hu_congr <;> push_cast <;> ring

theorem Hu_y_pow (h : HeisRel A B C σ) (y : K) (k : ℕ) : (Hu h 0 y 0) ^ k = Hu h 0 (k * y) 0 := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact (Hu_zero h).symm
  | succ k ih =>
    rw [pow_succ, ih, Hu_mul]
    apply Hu_congr <;> push_cast <;> ring

theorem comm_Hu (h : HeisRel A B C σ) : ⁅Hu h 0 1 0, Hu h 1 0 0⁆ = Hu h 0 0 (-2 * σ) := by
  rw [commutatorElement_def, Hu_inv, Hu_inv, Hu_mul, Hu_mul, Hu_mul]
  apply Hu_congr <;> ring

theorem Hu_central_comm (h : HeisRel A B C σ) (c x y z : K) :
    Hu h 0 0 c * Hu h x y z = Hu h x y z * Hu h 0 0 c := by
  rw [Hu_mul, Hu_mul]
  apply Hu_congr <;> ring

end Heis

end CFSG.CGT.PushingUpLit.CGT6M
