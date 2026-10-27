module

public import Certificates.Data.CFSGNative.Timmesfeld.M3B
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.KC.M3BIrr

open Timmesfeld.M3B

@[expose] def fz (x : F3) : ZMod 3 := x

theorem fz_add (x y : F3) : fz (x + y) = fz x + fz y := rfl
theorem fz_mul (x y : F3) : fz (x * y) = fz x * fz y := rfl
theorem fz_zero : fz 0 = 0 := rfl
theorem fz_one : fz 1 = 1 := rfl
theorem fz_inj {x y : F3} (h : fz x = fz y) : x = y := h

@[expose] def toM (A : Mat) : Matrix (Fin 12) (Fin 12) (ZMod 3) := Matrix.of fun i j => fz (mget A i j)

theorem toM_apply (A : Mat) (i j : Fin 12) : toM A i j = fz (mget A i j) := rfl

theorem mget_mofFn (f : Fin 12 → Fin 12 → F3) (i j : Fin 12) : mget (mofFn f) i j = f i j := by
  simp [mget, vget, mofFn, vofFn, getElem!_def]

theorem toM_mofFn (f : Fin 12 → Fin 12 → F3) (i j : Fin 12) : toM (mofFn f) i j = fz (f i j) := by
  rw [toM_apply, mget_mofFn]

theorem fsum_eq : ∀ (n : ℕ) (f : Fin n → F3), fz (fsum n f) = ∑ i, fz (f i)
  | 0, f => rfl
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc, ← fsum_eq n]
    unfold fsum
    rw [Fin.foldl_succ_last, fz_add]

theorem toM_mmul (A B : Mat) : toM (mmul A B) = toM A * toM B := by
  ext i j
  rw [Matrix.mul_apply]
  unfold mmul
  rw [toM_mofFn, fsum_eq]
  simp only [fz_mul, toM_apply]

theorem toM_mone : toM mone = 1 := by
  ext i j
  unfold mone
  rw [toM_mofFn, Matrix.one_apply]
  split
  · exact fz_one
  · exact fz_zero

theorem toM_mpow (A : Mat) : ∀ n : ℕ, toM (mpow A n) = toM A ^ n
  | 0 => by rw [mpow.eq_def, toM_mone, pow_zero]
  | n + 1 => by
    rw [mpow.eq_def]
    dsimp only
    rw [toM_mmul, toM_mpow A n, pow_succ]

theorem toM_eq_of_meq {A B : Mat} (h : meq A B = true) : toM A = toM B := by
  ext i j
  unfold meq at h
  simp only [List.all_eq_true, List.mem_finRange, beq_iff_eq, forall_const] at h
  rw [toM_apply, toM_apply, h i j]

end CFSG.KC.M3BIrr

end
