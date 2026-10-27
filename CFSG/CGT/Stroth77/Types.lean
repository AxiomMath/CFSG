module

public import CFSG.CGT.Stroth77.SigmaFour
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type100

section

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 1, m + 1]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]
@[expose] def uvA : Fin 3 → ℤ := ![2, 1, 2]
@[expose] def tM : IntMat :=
  ofCols ![1, 2, 0] ![0, -1, 0] (ρM *ᵥ uvA)
@[expose] def uvM : IntMat :=
  ofCols ![-3, -2, -2] uvA (ρM *ᵥ (tM *ᵥ uvA))
@[expose] def uM : IntMat := uMat ![1, 0, 0] (0)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (m : ℕ) : Compat (k m) uvM :=
  Compat.of_witness (C := !![-3, 4, 4; -1, 1, 2; -1, 2, 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (m : ℕ) : Compat (k m) tM :=
  Compat.of_witness (C := !![1, 0, -4; 1, -1, -2; 0, 0, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (m : ℕ) : Compat (k m) uM :=
  Compat.of_witness (C := !![1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (m : ℕ) : Compat (k m) ρM :=
  Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (m : ℕ) :
    MatEq (k m) (uvM * uvM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (m : ℕ) :
    MatEq (k m) (tM * tM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (m : ℕ) :
    MatEq (k m) (tM * uvM) (uvM * tM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (m : ℕ) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (m : ℕ) :
    MatEq (k m) (uM * uM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (m : ℕ) :
    MatEq (k m) (ρM * (uM * (ρM * uM))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (m : ℕ) :
    MatEq (k m) (ρM * uvM) (tM * ρM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (m : ℕ) :
    MatEq (k m) (ρM * tM) (tM * (uvM * ρM)) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (m : ℕ) :
    MatEq (k m) (uM * uvM) (uvM * uM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (m : ℕ) :
    MatEq (k m) (uM * tM) (tM * (uvM * uM)) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (m : ℕ) : SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq uvM tM uM ρM
    (compat_uv m) (compat_t m) (compat_u m) (compat_rho m)
    (uv_sq m) (t_sq m) (uv_comm_t m) (rho_cube m) (u_sq m) (u_rho m) (uv_rho m) (t_rho m) (uv_comm_u m) (t_u m)

theorem uv_c (m : ℕ) :
    (action m).φuv Torus.c = (-3 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv m) 0 (-3) (-2) (-2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (m : ℕ) :
    (action m).φuv Torus.a = (2 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv m) 1 (2) (1) (2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (m : ℕ) :
    (action m).φuv Torus.b = (2 : ℤ) • Torus.c + (2 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv m) 2 (2) (2) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (m : ℕ) :
    (action m).φt Torus.c = (1 : ℤ) • Torus.c + (2 : ℤ) • Torus.a := by
  refine (matAct_gen_of tM (compat_t m) 0 (1) (2) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (m : ℕ) :
    (action m).φt Torus.a = (-1 : ℤ) • Torus.a := by
  refine (matAct_gen_of tM (compat_t m) 1 (0) (-1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (m : ℕ) :
    (action m).φt Torus.b = (-2 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of tM (compat_t m) 2 (-2) (-2) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (m : ℕ) :
    (action m).φu Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of uM (compat_u m) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (m : ℕ) :
    (action m).φu Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of uM (compat_u m) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (m : ℕ) :
    (action m).φu Torus.b = (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of uM (compat_u m) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (m : ℕ) :
    (action m).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of ρM (compat_rho m) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (m : ℕ) :
    (action m).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of ρM (compat_rho m) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (m : ℕ) :
    (action m).φρ Torus.b = (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of ρM (compat_rho m) 2 (-2) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end

end Type100

namespace Type200

section

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 2, m + 2]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]
@[expose] def uvA : Fin 3 → ℤ := ![1, 1, 2]
@[expose] def tM : IntMat :=
  ofCols ![1, 4, 0] ![0, -1, 0] (ρM *ᵥ uvA)
@[expose] def uvM : IntMat :=
  ofCols ![-3, -4, -4] uvA (ρM *ᵥ (tM *ᵥ uvA))
@[expose] def uM : IntMat := uMat ![1, 0, 0] (0)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (m : ℕ) : Compat (k m) uvM :=
  Compat.of_witness (C := !![-3, 4, 4; -1, 1, 2; -1, 2, 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (m : ℕ) : Compat (k m) tM :=
  Compat.of_witness (C := !![1, 0, -4; 1, -1, -2; 0, 0, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (m : ℕ) : Compat (k m) uM :=
  Compat.of_witness (C := !![1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (m : ℕ) : Compat (k m) ρM :=
  Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (m : ℕ) :
    MatEq (k m) (uvM * uvM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (m : ℕ) :
    MatEq (k m) (tM * tM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (m : ℕ) :
    MatEq (k m) (tM * uvM) (uvM * tM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (m : ℕ) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (m : ℕ) :
    MatEq (k m) (uM * uM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (m : ℕ) :
    MatEq (k m) (ρM * (uM * (ρM * uM))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (m : ℕ) :
    MatEq (k m) (ρM * uvM) (tM * ρM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (m : ℕ) :
    MatEq (k m) (ρM * tM) (tM * (uvM * ρM)) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (m : ℕ) :
    MatEq (k m) (uM * uvM) (uvM * uM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (m : ℕ) :
    MatEq (k m) (uM * tM) (tM * (uvM * uM)) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (m : ℕ) : SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq uvM tM uM ρM
    (compat_uv m) (compat_t m) (compat_u m) (compat_rho m)
    (uv_sq m) (t_sq m) (uv_comm_t m) (rho_cube m) (u_sq m) (u_rho m) (uv_rho m) (t_rho m) (uv_comm_u m) (t_u m)

theorem uv_c (m : ℕ) :
    (action m).φuv Torus.c = (-3 : ℤ) • Torus.c + (-4 : ℤ) • Torus.a + (-4 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv m) 0 (-3) (-4) (-4) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (m : ℕ) :
    (action m).φuv Torus.a = (1 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv m) 1 (1) (1) (2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (m : ℕ) :
    (action m).φuv Torus.b = (1 : ℤ) • Torus.c + (2 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv m) 2 (1) (2) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (m : ℕ) :
    (action m).φt Torus.c = (1 : ℤ) • Torus.c + (4 : ℤ) • Torus.a := by
  refine (matAct_gen_of tM (compat_t m) 0 (1) (4) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (m : ℕ) :
    (action m).φt Torus.a = (-1 : ℤ) • Torus.a := by
  refine (matAct_gen_of tM (compat_t m) 1 (0) (-1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (m : ℕ) :
    (action m).φt Torus.b = (-1 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of tM (compat_t m) 2 (-1) (-2) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (m : ℕ) :
    (action m).φu Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of uM (compat_u m) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (m : ℕ) :
    (action m).φu Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of uM (compat_u m) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (m : ℕ) :
    (action m).φu Torus.b = (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of uM (compat_u m) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (m : ℕ) :
    (action m).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of ρM (compat_rho m) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (m : ℕ) :
    (action m).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of ρM (compat_rho m) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (m : ℕ) :
    (action m).φρ Torus.b = (-1 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of ρM (compat_rho m) 2 (-1) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end

end Type200

namespace Type201

section

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 2, m + 2]

@[expose] def ρM (m : ℕ) : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]
@[expose] def uvA (m : ℕ) : Fin 3 → ℤ := ![1, 1, 2+(2 ^ (m + 1))]
@[expose] def tM (m : ℕ) : IntMat :=
  ofCols ![1, 4, 0] ![0, -1+(2 ^ (m + 1)), 0] (ρM m *ᵥ uvA m)
@[expose] def uvM (m : ℕ) : IntMat :=
  ofCols ![-3, -4, -4] (uvA m) (ρM m *ᵥ (tM m *ᵥ uvA m))
@[expose] def uM (m : ℕ) : IntMat := uMat ![1, 0, 0] (0)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (m : ℕ) : Compat (k m) (uvM m) :=
  Compat.of_witness (C := !![-3, 4, 4; -1, 1, 4*(2 ^ m)^2 + 6*(2 ^ m) + 2; -1, 2*(2 ^ m) + 2, 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (m : ℕ) : Compat (k m) (tM m) :=
  Compat.of_witness (C := !![1, 0, -8*(2 ^ m) - 4; 1, 2*(2 ^ m) - 1, -2*(2 ^ m) - 2; 0, 0, -2*(2 ^ m) - 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (m : ℕ) : Compat (k m) (uM m) :=
  Compat.of_witness (C := !![1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (m : ℕ) : Compat (k m) (ρM m) :=
  Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (m : ℕ) :
    MatEq (k m) ((uvM m) * (uvM m)) (1) :=
  MatEq.of_witness (W := !![0, 2, 4*(2 ^ m) + 6; -4*(2 ^ m) - 6, 2*(2 ^ m)^2 + 5*(2 ^ m) + 4, 2*(2 ^ m) + 3; -2, 1, 2*(2 ^ m)^2 + 5*(2 ^ m) + 4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (m : ℕ) :
    MatEq (k m) ((tM m) * (tM m)) (1) :=
  MatEq.of_witness (W := !![0, 0, 4*(2 ^ m) + 2; 2, (2 ^ m) - 1, -1; 0, 0, (2 ^ m) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (m : ℕ) :
    MatEq (k m) ((tM m) * (uvM m)) ((uvM m) * (tM m)) :=
  MatEq.of_witness (W := !![8, -4*(2 ^ m) - 8, -4; 0, -(2 ^ m) - 2, 4*(2 ^ m)^2 + 6*(2 ^ m); 0, -2*(2 ^ m) - 2, (2 ^ m)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (m : ℕ) :
    MatEq (k m) ((ρM m) * ((ρM m) * (ρM m))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (m : ℕ) :
    MatEq (k m) ((uM m) * (uM m)) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (m : ℕ) :
    MatEq (k m) ((ρM m) * ((uM m) * ((ρM m) * (uM m)))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (m : ℕ) :
    MatEq (k m) ((ρM m) * (uvM m)) ((tM m) * (ρM m)) :=
  MatEq.of_witness (W := !![0, 0, -2; 0, 0, 0; 0, 0, (2 ^ m) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (m : ℕ) :
    MatEq (k m) ((ρM m) * (tM m)) ((tM m) * ((uvM m) * (ρM m))) :=
  MatEq.of_witness (W := !![-8, 2, -4*(2 ^ m); 0, -2*(2 ^ m)^2 - 2*(2 ^ m) + 1, 2*(2 ^ m)^2 + (2 ^ m) - 2; -2, 1, -(2 ^ m)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (m : ℕ) :
    MatEq (k m) ((uM m) * (uvM m)) ((uvM m) * (uM m)) :=
  MatEq.of_witness (W := !![0, 0, 0; 0, -(2 ^ m) - 1, 0; 0, 0, (2 ^ m) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (m : ℕ) :
    MatEq (k m) ((uM m) * (tM m)) ((tM m) * ((uvM m) * (uM m))) :=
  MatEq.of_witness (W := !![-8, 2, 4*(2 ^ m) + 4; 0, -2*(2 ^ m)^2 - 2*(2 ^ m) + 1, (2 ^ m) + 1; -2, 1, (2 ^ m) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (m : ℕ) : SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM m) (tM m) (uM m) (ρM m)
    (compat_uv m) (compat_t m) (compat_u m) (compat_rho m)
    (uv_sq m) (t_sq m) (uv_comm_t m) (rho_cube m) (u_sq m) (u_rho m) (uv_rho m) (t_rho m) (uv_comm_u m) (t_u m)

theorem uv_c (m : ℕ) :
    (action m).φuv Torus.c = (-3 : ℤ) • Torus.c + (-4 : ℤ) • Torus.a + (-4 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM m) (compat_uv m) 0 (-3) (-4) (-4) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (m : ℕ) :
    (action m).φuv Torus.a = (1 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2*(2 ^ m) + 2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM m) (compat_uv m) 1 (1) (1) (2*(2 ^ m) + 2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (m : ℕ) :
    (action m).φuv Torus.b = (1 : ℤ) • Torus.c + (4*(2 ^ m)^2 + 6*(2 ^ m) + 2 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM m) (compat_uv m) 2 (1) (4*(2 ^ m)^2 + 6*(2 ^ m) + 2) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (m : ℕ) :
    (action m).φt Torus.c = (1 : ℤ) • Torus.c + (4 : ℤ) • Torus.a := by
  refine (matAct_gen_of (tM m) (compat_t m) 0 (1) (4) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (m : ℕ) :
    (action m).φt Torus.a = (2*(2 ^ m) - 1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (tM m) (compat_t m) 1 (0) (2*(2 ^ m) - 1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (m : ℕ) :
    (action m).φt Torus.b = (-2*(2 ^ m) - 1 : ℤ) • Torus.c + (-2*(2 ^ m) - 2 : ℤ) • Torus.a + (-2*(2 ^ m) - 1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM m) (compat_t m) 2 (-2*(2 ^ m) - 1) (-2*(2 ^ m) - 2) (-2*(2 ^ m) - 1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (m : ℕ) :
    (action m).φu Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (uM m) (compat_u m) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (m : ℕ) :
    (action m).φu Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uM m) (compat_u m) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (m : ℕ) :
    (action m).φu Torus.b = (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (uM m) (compat_u m) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (m : ℕ) :
    (action m).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (ρM m) (compat_rho m) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (m : ℕ) :
    (action m).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM m) (compat_rho m) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (m : ℕ) :
    (action m).φρ Torus.b = (-1 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM m) (compat_rho m) 2 (-1) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end

end Type201

end CFSG.CGT.Stroth77
