module

public import CFSG.CGT.Stroth77.SigmaFour
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type101

section

@[expose] def k (s : ℕ) : Fin 3 → ℕ := ![s + 1, s + 2, s + 2]

@[expose] def ρM (s : ℕ) : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]
@[expose] def uvA (s : ℕ) : Fin 3 → ℤ := ![2, 1, 2+(2 ^ (s + 1))]
@[expose] def tM (s : ℕ) : IntMat :=
  ofCols ![1, 2, 0] ![0, -1+(2 ^ (s + 1)), 0] (ρM s *ᵥ uvA s)
@[expose] def uvM (s : ℕ) : IntMat :=
  ofCols ![-3, -2, -2] (uvA s) (ρM s *ᵥ (tM s *ᵥ uvA s))
@[expose] def uM (s : ℕ) : IntMat := uMat ![1, 0, 0] (0)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (s : ℕ) : Compat (k s) (uvM s) :=
  Compat.of_witness (C := !![-3, 4, 4; -1, 1, 4*(2 ^ s)^2 + 6*(2 ^ s) + 2; -1, 2*(2 ^ s) + 2, 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (s : ℕ) : Compat (k s) (tM s) :=
  Compat.of_witness (C := !![1, 0, -8*(2 ^ s) - 4; 1, 2*(2 ^ s) - 1, -2*(2 ^ s) - 2; 0, 0, -2*(2 ^ s) - 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (s : ℕ) : Compat (k s) (uM s) :=
  Compat.of_witness (C := !![1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (s : ℕ) : Compat (k s) (ρM s) :=
  Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (s : ℕ) :
    MatEq (k s) ((uvM s) * (uvM s)) (1) :=
  MatEq.of_witness (W := !![0, 2, 4*(2 ^ s) + 6; -2*(2 ^ s) - 3, 2*(2 ^ s)^2 + 5*(2 ^ s) + 4, 2*(2 ^ s) + 3; -1, 1, 2*(2 ^ s)^2 + 5*(2 ^ s) + 4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (s : ℕ) :
    MatEq (k s) ((tM s) * (tM s)) (1) :=
  MatEq.of_witness (W := !![0, 0, 4*(2 ^ s) + 2; 1, (2 ^ s) - 1, -1; 0, 0, (2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (s : ℕ) :
    MatEq (k s) ((tM s) * (uvM s)) ((uvM s) * (tM s)) :=
  MatEq.of_witness (W := !![4, -4*(2 ^ s) - 8, -4; 0, -(2 ^ s) - 2, 4*(2 ^ s)^2 + 6*(2 ^ s); 0, -2*(2 ^ s) - 2, (2 ^ s)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (s : ℕ) :
    MatEq (k s) ((ρM s) * ((ρM s) * (ρM s))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (s : ℕ) :
    MatEq (k s) ((uM s) * (uM s)) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (s : ℕ) :
    MatEq (k s) ((ρM s) * ((uM s) * ((ρM s) * (uM s)))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (s : ℕ) :
    MatEq (k s) ((ρM s) * (uvM s)) ((tM s) * (ρM s)) :=
  MatEq.of_witness (W := !![0, 0, -2; 0, 0, 0; 0, 0, (2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (s : ℕ) :
    MatEq (k s) ((ρM s) * (tM s)) ((tM s) * ((uvM s) * (ρM s))) :=
  MatEq.of_witness (W := !![-4, 2, -4*(2 ^ s); 0, -2*(2 ^ s)^2 - 2*(2 ^ s) + 1, 2*(2 ^ s)^2 + (2 ^ s) - 2; -1, 1, -(2 ^ s)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (s : ℕ) :
    MatEq (k s) ((uM s) * (uvM s)) ((uvM s) * (uM s)) :=
  MatEq.of_witness (W := !![0, 0, 0; 0, -(2 ^ s) - 1, 0; 0, 0, (2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (s : ℕ) :
    MatEq (k s) ((uM s) * (tM s)) ((tM s) * ((uvM s) * (uM s))) :=
  MatEq.of_witness (W := !![-4, 2, 4*(2 ^ s) + 4; 0, -2*(2 ^ s)^2 - 2*(2 ^ s) + 1, (2 ^ s) + 1; -1, 1, (2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (s : ℕ) : SigmaFourAction (k s) :=
  SigmaFourAction.ofMatEq (uvM s) (tM s) (uM s) (ρM s)
    (compat_uv s) (compat_t s) (compat_u s) (compat_rho s)
    (uv_sq s) (t_sq s) (uv_comm_t s) (rho_cube s) (u_sq s) (u_rho s) (uv_rho s) (t_rho s) (uv_comm_u s) (t_u s)

theorem uv_c (s : ℕ) :
    (action s).φuv Torus.c = (-3 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM s) (compat_uv s) 0 (-3) (-2) (-2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (s : ℕ) :
    (action s).φuv Torus.a = (2 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2*(2 ^ s) + 2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM s) (compat_uv s) 1 (2) (1) (2*(2 ^ s) + 2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (s : ℕ) :
    (action s).φuv Torus.b = (2 : ℤ) • Torus.c + (4*(2 ^ s)^2 + 6*(2 ^ s) + 2 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM s) (compat_uv s) 2 (2) (4*(2 ^ s)^2 + 6*(2 ^ s) + 2) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (s : ℕ) :
    (action s).φt Torus.c = (1 : ℤ) • Torus.c + (2 : ℤ) • Torus.a := by
  refine (matAct_gen_of (tM s) (compat_t s) 0 (1) (2) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (s : ℕ) :
    (action s).φt Torus.a = (2*(2 ^ s) - 1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (tM s) (compat_t s) 1 (0) (2*(2 ^ s) - 1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (s : ℕ) :
    (action s).φt Torus.b = (-4*(2 ^ s) - 2 : ℤ) • Torus.c + (-2*(2 ^ s) - 2 : ℤ) • Torus.a + (-2*(2 ^ s) - 1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM s) (compat_t s) 2 (-4*(2 ^ s) - 2) (-2*(2 ^ s) - 2) (-2*(2 ^ s) - 1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (s : ℕ) :
    (action s).φu Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (uM s) (compat_u s) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (s : ℕ) :
    (action s).φu Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uM s) (compat_u s) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (s : ℕ) :
    (action s).φu Torus.b = (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (uM s) (compat_u s) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (s : ℕ) :
    (action s).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (ρM s) (compat_rho s) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (s : ℕ) :
    (action s).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM s) (compat_rho s) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (s : ℕ) :
    (action s).φρ Torus.b = (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM s) (compat_rho s) 2 (-2) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end

end Type101

namespace Type110

section

@[expose] def k (t : ℕ) : Fin 3 → ℕ := ![t + 2, t + 3, t + 3]

@[expose] def ρM (t : ℕ) : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]
@[expose] def uvA (t : ℕ) : Fin 3 → ℤ := ![2, 1, 2]
@[expose] def tM (t : ℕ) : IntMat :=
  ofCols ![1, 2, (2 ^ (t + 2))] ![0, -1, 0] (ρM t *ᵥ uvA t)
@[expose] def uvM (t : ℕ) : IntMat :=
  ofCols ![-3, -2+(2 ^ (t + 2)), -2] (uvA t) (ρM t *ᵥ (tM t *ᵥ uvA t))
@[expose] def uM (t : ℕ) : IntMat := uMat ![1+(2 ^ (t + 1)), 0, 0] (0)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (t : ℕ) : Compat (k t) (uvM t) :=
  Compat.of_witness (C := !![-3, 4, 4 - 32*(2 ^ t); 2*(2 ^ t) - 1, 1, 2 - 8*(2 ^ t); -1, 2, 1 - 8*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (t : ℕ) : Compat (k t) (tM t) :=
  Compat.of_witness (C := !![1, 0, -4; 1, -1, -2; 2*(2 ^ t), 0, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (t : ℕ) : Compat (k t) (uM t) :=
  Compat.of_witness (C := !![2*(2 ^ t) + 1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (t : ℕ) : Compat (k t) (ρM t) :=
  Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (t : ℕ) :
    MatEq (k t) ((uvM t) * (uvM t)) (1) :=
  MatEq.of_witness (W := !![10, -8, 32*(2 ^ t); 1, -1, 1; 3, -2, 8*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (t : ℕ) :
    MatEq (k t) ((tM t) * (tM t)) (1) :=
  MatEq.of_witness (W := !![-2, 0, 0; -1, 0, 0; 0, 0, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (t : ℕ) :
    MatEq (k t) ((tM t) * (uvM t)) ((uvM t) * (tM t)) :=
  MatEq.of_witness (W := !![16*(2 ^ t) - 2, 0, -4; 4*(2 ^ t) - 2, 0, -1; 4*(2 ^ t) - 2, 1, 1 - 8*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (t : ℕ) :
    MatEq (k t) ((ρM t) * ((ρM t) * (ρM t))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (t : ℕ) :
    MatEq (k t) ((uM t) * (uM t)) (1) :=
  MatEq.of_witness (W := !![(2 ^ t) + 1, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (t : ℕ) :
    MatEq (k t) ((ρM t) * ((uM t) * ((ρM t) * (uM t)))) (1) :=
  MatEq.of_witness (W := !![(2 ^ t) + 1, -1, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (t : ℕ) :
    MatEq (k t) ((ρM t) * (uvM t)) ((tM t) * (ρM t)) :=
  MatEq.of_witness (W := !![0, 0, 0; 0, 0, 1; 0, 0, 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (t : ℕ) :
    MatEq (k t) ((ρM t) * (tM t)) ((tM t) * ((uvM t) * (ρM t))) :=
  MatEq.of_witness (W := !![-2, 0, 0; 0, 1, -2; 1, 8*(2 ^ t) - 2, -8*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (t : ℕ) :
    MatEq (k t) ((uM t) * (uvM t)) ((uvM t) * (uM t)) :=
  MatEq.of_witness (W := !![0, 5, -8*(2 ^ t) - 3; -(2 ^ t), 1, -1; 1, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (t : ℕ) :
    MatEq (k t) ((uM t) * (tM t)) ((tM t) * ((uvM t) * (uM t))) :=
  MatEq.of_witness (W := !![0, 0, -1; (2 ^ t) + 1, 1, 0; 3*(2 ^ t) + 1, 8*(2 ^ t) - 2, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (t : ℕ) : SigmaFourAction (k t) :=
  SigmaFourAction.ofMatEq (uvM t) (tM t) (uM t) (ρM t)
    (compat_uv t) (compat_t t) (compat_u t) (compat_rho t)
    (uv_sq t) (t_sq t) (uv_comm_t t) (rho_cube t) (u_sq t) (u_rho t) (uv_rho t) (t_rho t) (uv_comm_u t) (t_u t)

theorem uv_c (t : ℕ) :
    (action t).φuv Torus.c = (-3 : ℤ) • Torus.c + (4*(2 ^ t) - 2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM t) (compat_uv t) 0 (-3) (4*(2 ^ t) - 2) (-2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (t : ℕ) :
    (action t).φuv Torus.a = (2 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM t) (compat_uv t) 1 (2) (1) (2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (t : ℕ) :
    (action t).φuv Torus.b = (2 - 16*(2 ^ t) : ℤ) • Torus.c + (2 - 8*(2 ^ t) : ℤ) • Torus.a + (1 - 8*(2 ^ t) : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM t) (compat_uv t) 2 (2 - 16*(2 ^ t)) (2 - 8*(2 ^ t)) (1 - 8*(2 ^ t)) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (t : ℕ) :
    (action t).φt Torus.c = (1 : ℤ) • Torus.c + (2 : ℤ) • Torus.a + (4*(2 ^ t) : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM t) (compat_t t) 0 (1) (2) (4*(2 ^ t)) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (t : ℕ) :
    (action t).φt Torus.a = (-1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (tM t) (compat_t t) 1 (0) (-1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (t : ℕ) :
    (action t).φt Torus.b = (-2 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM t) (compat_t t) 2 (-2) (-2) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (t : ℕ) :
    (action t).φu Torus.c = (2*(2 ^ t) + 1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (uM t) (compat_u t) 0 (2*(2 ^ t) + 1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (t : ℕ) :
    (action t).φu Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uM t) (compat_u t) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (t : ℕ) :
    (action t).φu Torus.b = (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (uM t) (compat_u t) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (t : ℕ) :
    (action t).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (ρM t) (compat_rho t) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (t : ℕ) :
    (action t).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM t) (compat_rho t) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (t : ℕ) :
    (action t).φρ Torus.b = (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM t) (compat_rho t) 2 (-2) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end

end Type110

namespace Type111

section

@[expose] def k (t : ℕ) : Fin 3 → ℕ := ![t + 2, t + 3, t + 3]

@[expose] def ρM (t : ℕ) : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-2, -1, -1]
@[expose] def uvA (t : ℕ) : Fin 3 → ℤ := ![2, 1, 2+(2 ^ (t + 2))]
@[expose] def tM (t : ℕ) : IntMat :=
  ofCols ![1, 2, (2 ^ (t + 2))] ![0, -1+(2 ^ (t + 2)), 0] (ρM t *ᵥ uvA t)
@[expose] def uvM (t : ℕ) : IntMat :=
  ofCols ![-3, -2+(2 ^ (t + 2)), -2] (uvA t) (ρM t *ᵥ (tM t *ᵥ uvA t))
@[expose] def uM (t : ℕ) : IntMat := uMat ![1+(2 ^ (t + 1)), 0, 0] (0)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (t : ℕ) : Compat (k t) (uvM t) :=
  Compat.of_witness (C := !![-3, 4, 4 - 32*(2 ^ t); 2*(2 ^ t) - 1, 1, 16*(2 ^ t)^2 + 4*(2 ^ t) + 2; -1, 4*(2 ^ t) + 2, 1 - 8*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (t : ℕ) : Compat (k t) (tM t) :=
  Compat.of_witness (C := !![1, 0, -16*(2 ^ t) - 4; 1, 4*(2 ^ t) - 1, -4*(2 ^ t) - 2; 2*(2 ^ t), 0, -4*(2 ^ t) - 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (t : ℕ) : Compat (k t) (uM t) :=
  Compat.of_witness (C := !![2*(2 ^ t) + 1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (t : ℕ) : Compat (k t) (ρM t) :=
  Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (t : ℕ) :
    MatEq (k t) ((uvM t) * (uvM t)) (1) :=
  MatEq.of_witness (W := !![10, -16*(2 ^ t) - 6, 40*(2 ^ t) + 6; -4*(2 ^ t) - 2, 8*(2 ^ t)^2 + 6*(2 ^ t) + 3, -16*(2 ^ t)^2 - 8*(2 ^ t) + 4; 2*(2 ^ t) + 2, -4*(2 ^ t) - 1, 8*(2 ^ t)^2 + 14*(2 ^ t) + 4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (t : ℕ) :
    MatEq (k t) ((tM t) * (tM t)) (1) :=
  MatEq.of_witness (W := !![-8*(2 ^ t) - 2, 0, 8*(2 ^ t) + 2; -2*(2 ^ t), 2*(2 ^ t) - 1, -1; -2*(2 ^ t), 0, -2*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (t : ℕ) :
    MatEq (k t) ((tM t) * (uvM t)) ((uvM t) * (tM t)) :=
  MatEq.of_witness (W := !![16*(2 ^ t) + 2, -8*(2 ^ t) - 8, -8; -8*(2 ^ t)^2 - 2, -2*(2 ^ t) - 2, 16*(2 ^ t)^2 + 12*(2 ^ t) - 1; 4*(2 ^ t) - 2, -4*(2 ^ t) - 1, 1 - 6*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (t : ℕ) :
    MatEq (k t) ((ρM t) * ((ρM t) * (ρM t))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (t : ℕ) :
    MatEq (k t) ((uM t) * (uM t)) (1) :=
  MatEq.of_witness (W := !![(2 ^ t) + 1, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (t : ℕ) :
    MatEq (k t) ((ρM t) * ((uM t) * ((ρM t) * (uM t)))) (1) :=
  MatEq.of_witness (W := !![(2 ^ t) + 1, -1, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (t : ℕ) :
    MatEq (k t) ((ρM t) * (uvM t)) ((tM t) * (ρM t)) :=
  MatEq.of_witness (W := !![0, 0, -2; 0, 0, 1; 0, 0, 2*(2 ^ t) + 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (t : ℕ) :
    MatEq (k t) ((ρM t) * (tM t)) ((tM t) * ((uvM t) * (ρM t))) :=
  MatEq.of_witness (W := !![-6, 2 - 16*(2 ^ t), 8*(2 ^ t); -2*(2 ^ t), -8*(2 ^ t)^2 - 4*(2 ^ t) + 2, 8*(2 ^ t)^2 + 6*(2 ^ t) - 4; 0, 4*(2 ^ t) - 1, -6*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (t : ℕ) :
    MatEq (k t) ((uM t) * (uvM t)) ((uvM t) * (uM t)) :=
  MatEq.of_witness (W := !![0, 5, -8*(2 ^ t) - 3; -(2 ^ t), -2*(2 ^ t), -1; 1, 1, 2*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (t : ℕ) :
    MatEq (k t) ((uM t) * (tM t)) ((tM t) * ((uvM t) * (uM t))) :=
  MatEq.of_witness (W := !![-8*(2 ^ t) - 4, 2 - 16*(2 ^ t), 4*(2 ^ t) + 3; -4*(2 ^ t)^2 - (2 ^ t) + 1, -8*(2 ^ t)^2 - 4*(2 ^ t) + 2, 2*(2 ^ t) + 1; (2 ^ t), 4*(2 ^ t) - 1, 2*(2 ^ t)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (t : ℕ) : SigmaFourAction (k t) :=
  SigmaFourAction.ofMatEq (uvM t) (tM t) (uM t) (ρM t)
    (compat_uv t) (compat_t t) (compat_u t) (compat_rho t)
    (uv_sq t) (t_sq t) (uv_comm_t t) (rho_cube t) (u_sq t) (u_rho t) (uv_rho t) (t_rho t) (uv_comm_u t) (t_u t)

theorem uv_c (t : ℕ) :
    (action t).φuv Torus.c = (-3 : ℤ) • Torus.c + (4*(2 ^ t) - 2 : ℤ) • Torus.a + (-2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM t) (compat_uv t) 0 (-3) (4*(2 ^ t) - 2) (-2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (t : ℕ) :
    (action t).φuv Torus.a = (2 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (4*(2 ^ t) + 2 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM t) (compat_uv t) 1 (2) (1) (4*(2 ^ t) + 2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (t : ℕ) :
    (action t).φuv Torus.b = (2 - 16*(2 ^ t) : ℤ) • Torus.c + (16*(2 ^ t)^2 + 4*(2 ^ t) + 2 : ℤ) • Torus.a + (1 - 8*(2 ^ t) : ℤ) • Torus.b := by
  refine (matAct_gen_of (uvM t) (compat_uv t) 2 (2 - 16*(2 ^ t)) (16*(2 ^ t)^2 + 4*(2 ^ t) + 2) (1 - 8*(2 ^ t)) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (t : ℕ) :
    (action t).φt Torus.c = (1 : ℤ) • Torus.c + (2 : ℤ) • Torus.a + (4*(2 ^ t) : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM t) (compat_t t) 0 (1) (2) (4*(2 ^ t)) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (t : ℕ) :
    (action t).φt Torus.a = (4*(2 ^ t) - 1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (tM t) (compat_t t) 1 (0) (4*(2 ^ t) - 1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (t : ℕ) :
    (action t).φt Torus.b = (-8*(2 ^ t) - 2 : ℤ) • Torus.c + (-4*(2 ^ t) - 2 : ℤ) • Torus.a + (-4*(2 ^ t) - 1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (tM t) (compat_t t) 2 (-8*(2 ^ t) - 2) (-4*(2 ^ t) - 2) (-4*(2 ^ t) - 1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (t : ℕ) :
    (action t).φu Torus.c = (2*(2 ^ t) + 1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (uM t) (compat_u t) 0 (2*(2 ^ t) + 1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (t : ℕ) :
    (action t).φu Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (uM t) (compat_u t) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (t : ℕ) :
    (action t).φu Torus.b = (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of (uM t) (compat_u t) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (t : ℕ) :
    (action t).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of (ρM t) (compat_rho t) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (t : ℕ) :
    (action t).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM t) (compat_rho t) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (t : ℕ) :
    (action t).φρ Torus.b = (-2 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of (ρM t) (compat_rho t) 2 (-2) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end

end Type111

namespace Type300

section

@[expose] def k (n : ℕ) : Fin 3 → ℕ := ![n, n, n]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-4, -1, -1]
@[expose] def uvA : Fin 3 → ℤ := ![4, 1, 2]
@[expose] def tM : IntMat :=
  ofCols ![1, 1, 0] ![0, -1, 0] (ρM *ᵥ uvA)
@[expose] def uvM : IntMat :=
  ofCols ![-3, -1, -1] uvA (ρM *ᵥ (tM *ᵥ uvA))
@[expose] def uM : IntMat := uMat ![1, 0, 0] (0)

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv (n : ℕ) : Compat (k n) uvM :=
  Compat.of_witness (C := !![-3, 4, 4; -1, 1, 2; -1, 2, 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (n : ℕ) : Compat (k n) tM :=
  Compat.of_witness (C := !![1, 0, -4; 1, -1, -2; 0, 0, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (n : ℕ) : Compat (k n) uM :=
  Compat.of_witness (C := !![1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (n : ℕ) : Compat (k n) ρM :=
  Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (n : ℕ) :
    MatEq (k n) (uvM * uvM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (n : ℕ) :
    MatEq (k n) (tM * tM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (n : ℕ) :
    MatEq (k n) (tM * uvM) (uvM * tM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (n : ℕ) :
    MatEq (k n) (ρM * (ρM * ρM)) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (n : ℕ) :
    MatEq (k n) (uM * uM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (n : ℕ) :
    MatEq (k n) (ρM * (uM * (ρM * uM))) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (n : ℕ) :
    MatEq (k n) (ρM * uvM) (tM * ρM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (n : ℕ) :
    MatEq (k n) (ρM * tM) (tM * (uvM * ρM)) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (n : ℕ) :
    MatEq (k n) (uM * uvM) (uvM * uM) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (n : ℕ) :
    MatEq (k n) (uM * tM) (tM * (uvM * uM)) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (n : ℕ) : SigmaFourAction (k n) :=
  SigmaFourAction.ofMatEq uvM tM uM ρM
    (compat_uv n) (compat_t n) (compat_u n) (compat_rho n)
    (uv_sq n) (t_sq n) (uv_comm_t n) (rho_cube n) (u_sq n) (u_rho n) (uv_rho n) (t_rho n) (uv_comm_u n) (t_u n)

theorem uv_c (n : ℕ) :
    (action n).φuv Torus.c = (-3 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv n) 0 (-3) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (n : ℕ) :
    (action n).φuv Torus.a = (4 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv n) 1 (4) (1) (2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (n : ℕ) :
    (action n).φuv Torus.b = (4 : ℤ) • Torus.c + (2 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of uvM (compat_uv n) 2 (4) (2) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (n : ℕ) :
    (action n).φt Torus.c = (1 : ℤ) • Torus.c + (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of tM (compat_t n) 0 (1) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (n : ℕ) :
    (action n).φt Torus.a = (-1 : ℤ) • Torus.a := by
  refine (matAct_gen_of tM (compat_t n) 1 (0) (-1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (n : ℕ) :
    (action n).φt Torus.b = (-4 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of tM (compat_t n) 2 (-4) (-2) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (n : ℕ) :
    (action n).φu Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of uM (compat_u n) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (n : ℕ) :
    (action n).φu Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of uM (compat_u n) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (n : ℕ) :
    (action n).φu Torus.b = (1 : ℤ) • Torus.a := by
  refine (matAct_gen_of uM (compat_u n) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (n : ℕ) :
    (action n).φρ Torus.c = (1 : ℤ) • Torus.c := by
  refine (matAct_gen_of ρM (compat_rho n) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (n : ℕ) :
    (action n).φρ Torus.a = (1 : ℤ) • Torus.b := by
  refine (matAct_gen_of ρM (compat_rho n) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (n : ℕ) :
    (action n).φρ Torus.b = (-4 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  refine (matAct_gen_of ρM (compat_rho n) 2 (-4) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end

end Type300

end CFSG.CGT.Stroth77
