module

public import CFSG.CGT.Stroth77.SigmaFour
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type210

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 2, m + 2]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]

@[expose] def uvA (m : ℕ) : Fin 3 → ℤ :=
  ![2 * 2 ^ (m - 2) + 1, 1 + 8 * 2 ^ (m - 2), 2 - 4 * 2 ^ (m - 2)]

@[expose] def tM (m : ℕ) : IntMat :=
  ofCols ![1, 4, 8 * 2 ^ (m - 2)] ![2 * 2 ^ (m - 2), -1 - 4 * 2 ^ (m - 2), 8 * 2 ^ (m - 2)]
    (ρM *ᵥ uvA m)

@[expose] def uvM (m : ℕ) : IntMat :=
  ofCols ![-3, -4 + 8 * 2 ^ (m - 2), -4] (uvA m) (ρM *ᵥ (tM m *ᵥ uvA m))

@[expose] def uM (m : ℕ) : IntMat :=
  uMat ![2 * 2 ^ (m - 2) + 1, 0, 0] (2 * 2 ^ (m - 2))

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k Nat.add_sub_cancel

theorem compat_uv (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((uvM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![-3, 8*(2 ^ s) + 4, -160*(2 ^ s)^2 - 96*(2 ^ s) + 4; 2*(2 ^ s) - 1, 8*(2 ^ s) + 1, -32*(2 ^ s)^2 - 44*(2 ^ s) + 2; -1, -4*(2 ^ s) + 2, -80*(2 ^ s)^2 - 32*(2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((tM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![1, 8*(2 ^ s), 24*(2 ^ s) - 4; 1, -4*(2 ^ s) - 1, 4*(2 ^ s) - 2; 2*(2 ^ s), 8*(2 ^ s), 12*(2 ^ s) - 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((uM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![2*(2 ^ s) + 1, 8*(2 ^ s), -16*(2 ^ s)^2 - 8*(2 ^ s); 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (m : ℕ) (hm : 2 ≤ m) : Compat (k m) (ρM) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uvM m) * (uvM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![44*(2 ^ s) + 24, 40*(2 ^ s)^2 + 8*(2 ^ s) - 12, 800*(2 ^ s)^3 + 784*(2 ^ s)^2 + 162*(2 ^ s) - 6; 12*(2 ^ s) + 8, 8*(2 ^ s)^2 + 12*(2 ^ s) - 5, 160*(2 ^ s)^3 + 248*(2 ^ s)^2 + 50*(2 ^ s) - 2; 18*(2 ^ s) + 10, 20*(2 ^ s)^2 - 4*(2 ^ s) - 4, 400*(2 ^ s)^3 + 328*(2 ^ s)^2 + 71*(2 ^ s) - 4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((tM m) * (tM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![12*(2 ^ s), 10*(2 ^ s) - 2, 20*(2 ^ s) - 4; 2*(2 ^ s) - 2, 3*(2 ^ s), 2*(2 ^ s); 6*(2 ^ s) + 2, 5*(2 ^ s) - 1, 14*(2 ^ s) - 3]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((tM m) * (uvM m)) ((uvM m) * (tM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![80*(2 ^ s)^2 + 52*(2 ^ s) - 12, 80*(2 ^ s)^2 + 48*(2 ^ s) + 6, -16*(2 ^ s)^2; 16*(2 ^ s)^2 + 20*(2 ^ s) - 4, 16*(2 ^ s)^2 + 20*(2 ^ s) + 1, 12*(2 ^ s)^2 + 31*(2 ^ s) - 1; 40*(2 ^ s)^2 + 20*(2 ^ s) - 6, 40*(2 ^ s)^2 + 17*(2 ^ s) + 3, -36*(2 ^ s)^2 - 33*(2 ^ s) + 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (uM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![(2 ^ s) + 1, 0, -2*(2 ^ s)^2 - 2*(2 ^ s); 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * ((uM m) * (ρM * (uM m)))) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![(2 ^ s) + 1, 2*(2 ^ s), -2*(2 ^ s)^2 - 3*(2 ^ s) - 1; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (uvM m)) ((tM m) * ρM) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![0, 0, 10*(2 ^ s) + 4; 0, 0, 5*(2 ^ s) + 2; 0, 0, 3*(2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (tM m)) ((tM m) * ((uvM m) * ρM)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![-4*(2 ^ s) + 6, 136*(2 ^ s)^2 + 60*(2 ^ s) - 6, -136*(2 ^ s)^2 - 58*(2 ^ s); 2*(2 ^ s), 12*(2 ^ s)^2 - 5*(2 ^ s) - 1, -12*(2 ^ s)^2; -4*(2 ^ s) + 6, 96*(2 ^ s)^2 + 53*(2 ^ s) - 5, -96*(2 ^ s)^2 - 47*(2 ^ s)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (uvM m)) ((uvM m) * (uM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![8*(2 ^ s), 4*(2 ^ s)^2 + 15*(2 ^ s) + 8, 80*(2 ^ s)^3 + 36*(2 ^ s)^2 - 32*(2 ^ s) - 7; -(2 ^ s), (2 ^ s) + 3, 2*(2 ^ s)^2 - 5*(2 ^ s) - 3; 1, 5*(2 ^ s) + 3, -3*(2 ^ s) - 3]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (tM m)) ((tM m) * ((uvM m) * (uM m))) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![-16*(2 ^ s)^2 + 8*(2 ^ s) + 10, 120*(2 ^ s)^2 + 71*(2 ^ s) - 5, 16*(2 ^ s)^3 - 36*(2 ^ s)^2 - 13*(2 ^ s) - 4; 4*(2 ^ s)^2 + 3*(2 ^ s) + 1, 16*(2 ^ s)^2 - 4*(2 ^ s), -8*(2 ^ s)^3 - 6*(2 ^ s)^2 + 2*(2 ^ s); -8*(2 ^ s)^2 + 9*(2 ^ s) + 6, 88*(2 ^ s)^2 + 66*(2 ^ s) - 5, 16*(2 ^ s)^3 - 18*(2 ^ s)^2 - 14*(2 ^ s) - 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (m : ℕ) (hm : 2 ≤ m) : SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM m) (tM m) (uM m) ρM
    (compat_uv m hm) (compat_t m hm) (compat_u m hm) (compat_rho m hm)
    (uv_sq m hm) (t_sq m hm) (uv_comm_t m hm) (rho_cube m hm) (u_sq m hm) (u_rho m hm)
    (uv_rho m hm) (t_rho m hm) (uv_comm_u m hm) (t_u m hm)

theorem uv_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φuv Torus.a = (2*(2 ^ (m - 2)) + 1 : ℤ) • Torus.c + (8*(2 ^ (m - 2)) + 1 : ℤ) • Torus.a + (-4*(2 ^ (m - 2)) + 2 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uvM (s + 2))) (compat_uv (s + 2) hm) 1 (2*(2 ^ s) + 1) (8*(2 ^ s) + 1) (-4*(2 ^ s) + 2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φuv Torus.b = (-40*(2 ^ (m - 2))^2 - 24*(2 ^ (m - 2)) + 1 : ℤ) • Torus.c + (-32*(2 ^ (m - 2))^2 - 44*(2 ^ (m - 2)) + 2 : ℤ) • Torus.a + (-80*(2 ^ (m - 2))^2 - 32*(2 ^ (m - 2)) + 1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uvM (s + 2))) (compat_uv (s + 2) hm) 2 (-40*(2 ^ s)^2 - 24*(2 ^ s) + 1) (-32*(2 ^ s)^2 - 44*(2 ^ s) + 2) (-80*(2 ^ s)^2 - 32*(2 ^ s) + 1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.c = (2*(2 ^ (m - 2)) + 1 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 0 (2*(2 ^ s) + 1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.a = (2*(2 ^ (m - 2)) : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 1 (2*(2 ^ s)) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.b = (-4*(2 ^ (m - 2))^2 - 2*(2 ^ (m - 2)) : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 2 (-4*(2 ^ s)^2 - 2*(2 ^ s)) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.c = (1 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.a = (0 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.b = (-1 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 2 (-1) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end Type210

namespace Type211

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m + 2, m + 2]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-1, -1, -1]

@[expose] def uvA (m : ℕ) : Fin 3 → ℤ :=
  ![2 * 2 ^ (m - 2) + 1, 1 + 8 * 2 ^ (m - 2), 2 + 4 * 2 ^ (m - 2)]

@[expose] def tM (m : ℕ) : IntMat :=
  ofCols ![1, 4, 8 * 2 ^ (m - 2)] ![2 * 2 ^ (m - 2), -1 + 4 * 2 ^ (m - 2), 8 * 2 ^ (m - 2)]
    (ρM *ᵥ uvA m)

@[expose] def uvM (m : ℕ) : IntMat :=
  ofCols ![-3, -4 + 8 * 2 ^ (m - 2), -4] (uvA m) (ρM *ᵥ (tM m *ᵥ uvA m))

@[expose] def uM (m : ℕ) : IntMat :=
  uMat ![2 * 2 ^ (m - 2) + 1, 0, 0] (2 * 2 ^ (m - 2))

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k Nat.add_sub_cancel

theorem compat_uv (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((uvM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![-3, 8*(2 ^ s) + 4, -352*(2 ^ s)^2 - 96*(2 ^ s) + 4; 2*(2 ^ s) - 1, 8*(2 ^ s) + 1, -96*(2 ^ s)^2 - 20*(2 ^ s) + 2; -1, 4*(2 ^ s) + 2, -80*(2 ^ s)^2 - 32*(2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((tM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![1, 8*(2 ^ s), -8*(2 ^ s) - 4; 1, 4*(2 ^ s) - 1, -4*(2 ^ s) - 2; 2*(2 ^ s), 8*(2 ^ s), 4*(2 ^ s) - 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((uM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![2*(2 ^ s) + 1, 8*(2 ^ s), -16*(2 ^ s)^2 - 8*(2 ^ s); 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (m : ℕ) (hm : 2 ≤ m) : Compat (k m) (ρM) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uvM m) * (uvM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![92*(2 ^ s) + 24, -88*(2 ^ s)^2 - 64*(2 ^ s) - 10, 1760*(2 ^ s)^3 + 1136*(2 ^ s)^2 + 182*(2 ^ s); 28*(2 ^ s) + 2, -24*(2 ^ s)^2 - 12*(2 ^ s) - 1, 480*(2 ^ s)^3 + 200*(2 ^ s)^2 + 18*(2 ^ s) + 1; 22*(2 ^ s) + 8, -20*(2 ^ s)^2 - 16*(2 ^ s) - 3, 400*(2 ^ s)^3 + 296*(2 ^ s)^2 + 59*(2 ^ s)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((tM m) * (tM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![-4*(2 ^ s), -2*(2 ^ s) - 2, -4*(2 ^ s) - 2; -2*(2 ^ s), -(2 ^ s) - 1, -2*(2 ^ s) - 1; 2*(2 ^ s) + 2, 5*(2 ^ s) - 1, -2*(2 ^ s) - 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((tM m) * (uvM m)) ((uvM m) * (tM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![176*(2 ^ s)^2 + 52*(2 ^ s) - 4, 176*(2 ^ s)^2 + 48*(2 ^ s) - 2, 80*(2 ^ s)^2 + 8*(2 ^ s) - 4; 48*(2 ^ s)^2 + 12*(2 ^ s) - 4, 48*(2 ^ s)^2 + 8*(2 ^ s) - 1, 20*(2 ^ s)^2 - (2 ^ s) - 1; 40*(2 ^ s)^2 + 20*(2 ^ s) - 6, 40*(2 ^ s)^2 + 21*(2 ^ s) + 1, -92*(2 ^ s)^2 - 21*(2 ^ s) + 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (uM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![(2 ^ s) + 1, 0, -2*(2 ^ s)^2 - 2*(2 ^ s); 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * ((uM m) * (ρM * (uM m)))) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![(2 ^ s) + 1, 2*(2 ^ s), -2*(2 ^ s)^2 - 3*(2 ^ s) - 1; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (uvM m)) ((tM m) * ρM) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![0, 0, -2*(2 ^ s) + 2; 0, 0, 5*(2 ^ s) + 2; 0, 0, -(2 ^ s) + 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (tM m)) ((tM m) * ((uvM m) * ρM)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![-4*(2 ^ s) - 2, 8*(2 ^ s)^2 - 4*(2 ^ s) - 4, -8*(2 ^ s)^2 + 10*(2 ^ s); -2*(2 ^ s), 4*(2 ^ s)^2 + 3*(2 ^ s), -4*(2 ^ s)^2 - 2; -4*(2 ^ s) + 4, 112*(2 ^ s)^2 + 25*(2 ^ s) - 4, -112*(2 ^ s)^2 - 15*(2 ^ s)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (uvM m)) ((uvM m) * (uM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![8*(2 ^ s), -4*(2 ^ s)^2 + 23*(2 ^ s) + 8, 80*(2 ^ s)^3 - 20*(2 ^ s)^2 - 32*(2 ^ s) - 7; -(2 ^ s), 5*(2 ^ s) + 2, 2*(2 ^ s)^2 - 5*(2 ^ s) - 3; 1, 5*(2 ^ s) + 3, -7*(2 ^ s) - 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (tM m)) ((tM m) * ((uvM m) * (uM m))) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![-16*(2 ^ s)^2 - 8*(2 ^ s) + 2, -8*(2 ^ s)^2 - 5*(2 ^ s) - 3, 16*(2 ^ s)^3 + 4*(2 ^ s)^2 - 5*(2 ^ s); -4*(2 ^ s)^2 - (2 ^ s) + 1, 4*(2 ^ s) + 1, 8*(2 ^ s)^3 + 2*(2 ^ s)^2 - 2*(2 ^ s) + 1; -8*(2 ^ s)^2 + 5*(2 ^ s) + 4, 104*(2 ^ s)^2 + 34*(2 ^ s) - 4, 16*(2 ^ s)^3 - 10*(2 ^ s)^2 - 14*(2 ^ s) - 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (m : ℕ) (hm : 2 ≤ m) : SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM m) (tM m) (uM m) ρM
    (compat_uv m hm) (compat_t m hm) (compat_u m hm) (compat_rho m hm)
    (uv_sq m hm) (t_sq m hm) (uv_comm_t m hm) (rho_cube m hm) (u_sq m hm) (u_rho m hm)
    (uv_rho m hm) (t_rho m hm) (uv_comm_u m hm) (t_u m hm)

theorem uv_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φuv Torus.a = (2*(2 ^ (m - 2)) + 1 : ℤ) • Torus.c + (8*(2 ^ (m - 2)) + 1 : ℤ) • Torus.a + (4*(2 ^ (m - 2)) + 2 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uvM (s + 2))) (compat_uv (s + 2) hm) 1 (2*(2 ^ s) + 1) (8*(2 ^ s) + 1) (4*(2 ^ s) + 2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φuv Torus.b = (-88*(2 ^ (m - 2))^2 - 24*(2 ^ (m - 2)) + 1 : ℤ) • Torus.c + (-96*(2 ^ (m - 2))^2 - 20*(2 ^ (m - 2)) + 2 : ℤ) • Torus.a + (-80*(2 ^ (m - 2))^2 - 32*(2 ^ (m - 2)) + 1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uvM (s + 2))) (compat_uv (s + 2) hm) 2 (-88*(2 ^ s)^2 - 24*(2 ^ s) + 1) (-96*(2 ^ s)^2 - 20*(2 ^ s) + 2) (-80*(2 ^ s)^2 - 32*(2 ^ s) + 1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.c = (2*(2 ^ (m - 2)) + 1 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 0 (2*(2 ^ s) + 1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.a = (2*(2 ^ (m - 2)) : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 1 (2*(2 ^ s)) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.b = (-4*(2 ^ (m - 2))^2 - 2*(2 ^ (m - 2)) : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 2 (-4*(2 ^ s)^2 - 2*(2 ^ s)) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.c = (1 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.a = (0 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.b = (-1 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 2 (-1) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end Type211

namespace Type310

@[expose] def k (m : ℕ) : Fin 3 → ℕ := ![m, m, m]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![-4, -1, -1]

@[expose] def uvA : Fin 3 → ℤ := ![4, 1, 2]

@[expose] def tM (m : ℕ) : IntMat :=
  ofCols ![1, 1, 2 * 2 ^ (m - 2)] ![0, -1, 0] (ρM *ᵥ uvA)

@[expose] def uvM (m : ℕ) : IntMat :=
  ofCols ![-3, -1 + 2 * 2 ^ (m - 2), -1] uvA (ρM *ᵥ (tM m *ᵥ uvA))

@[expose] def uM (m : ℕ) : IntMat :=
  uMat ![2 * 2 ^ (m - 2) + 1, 0, 0] 0

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k Nat.add_sub_cancel

theorem compat_uv (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((uvM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![-3, 4, -32*(2 ^ s) + 4; 2*(2 ^ s) - 1, 1, -8*(2 ^ s) + 2; -1, 2, -8*(2 ^ s) + 1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_t (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((tM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![1, 0, -4; 1, -1, -2; 2*(2 ^ s), 0, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_u (m : ℕ) (hm : 2 ≤ m) : Compat (k m) ((uM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![2*(2 ^ s) + 1, 0, 0; 0, 0, 1; 0, 1, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem compat_rho (m : ℕ) (hm : 2 ≤ m) : Compat (k m) (ρM) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact Compat.of_witness (C := !![1, 0, -4; 0, 0, -1; 0, 1, -1]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uvM m) * (uvM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![10, -16, 64*(2 ^ s); 1, -2, 2; 3, -4, 16*(2 ^ s)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((tM m) * (tM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![-2, 0, 0; -1, 0, 0; 0, 0, -2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_t (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((tM m) * (uvM m)) ((uvM m) * (tM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![16*(2 ^ s) - 2, 0, -8; 4*(2 ^ s) - 2, 0, -2; 4*(2 ^ s) - 2, 2, -16*(2 ^ s) + 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem rho_cube (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (ρM * ρM)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_sq (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (uM m)) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![(2 ^ s) + 1, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem u_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * ((uM m) * (ρM * (uM m)))) (1) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![(2 ^ s) + 1, -2, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (uvM m)) ((tM m) * ρM) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![0, 0, 0; 0, 0, 2; 0, 0, 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_rho (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) (ρM * (tM m)) ((tM m) * ((uvM m) * ρM)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![-2, 0, 0; 0, 2, -4; 1, 16*(2 ^ s) - 4, -16*(2 ^ s)]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem uv_comm_u (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (uvM m)) ((uvM m) * (uM m)) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![0, 10, -16*(2 ^ s) - 6; -(2 ^ s), 2, -2; 1, 2, -2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

theorem t_u (m : ℕ) (hm : 2 ≤ m) :
    MatEq (k m) ((uM m) * (tM m)) ((tM m) * ((uvM m) * (uM m))) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  exact MatEq.of_witness (W := !![0, 0, -2; (2 ^ s) + 1, 2, 0; 3*(2 ^ s) + 1, 16*(2 ^ s) - 4, -2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1)

@[expose] def action (m : ℕ) (hm : 2 ≤ m) : SigmaFourAction (k m) :=
  SigmaFourAction.ofMatEq (uvM m) (tM m) (uM m) ρM
    (compat_uv m hm) (compat_t m hm) (compat_u m hm) (compat_rho m hm)
    (uv_sq m hm) (t_sq m hm) (uv_comm_t m hm) (rho_cube m hm) (u_sq m hm) (u_rho m hm)
    (uv_rho m hm) (t_rho m hm) (uv_comm_u m hm) (t_u m hm)

theorem uv_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φuv Torus.c = (-3 : ℤ) • Torus.c + (2*(2 ^ (m - 2)) - 1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uvM (s + 2))) (compat_uv (s + 2) hm) 0 (-3) (2*(2 ^ s) - 1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φuv Torus.a = (4 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uvM (s + 2))) (compat_uv (s + 2) hm) 1 (4) (1) (2) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem uv_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φuv Torus.b = (-32*(2 ^ (m - 2)) + 4 : ℤ) • Torus.c + (-8*(2 ^ (m - 2)) + 2 : ℤ) • Torus.a + (-8*(2 ^ (m - 2)) + 1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uvM (s + 2))) (compat_uv (s + 2) hm) 2 (-32*(2 ^ s) + 4) (-8*(2 ^ s) + 2) (-8*(2 ^ s) + 1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φt Torus.c = (1 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (2*(2 ^ (m - 2)) : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((tM (s + 2))) (compat_t (s + 2) hm) 0 (1) (1) (2*(2 ^ s)) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φt Torus.a = (0 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((tM (s + 2))) (compat_t (s + 2) hm) 1 (0) (-1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem t_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φt Torus.b = (-4 : ℤ) • Torus.c + (-2 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((tM (s + 2))) (compat_t (s + 2) hm) 2 (-4) (-2) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.c = (2*(2 ^ (m - 2)) + 1 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 0 (2*(2 ^ s) + 1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.a = (0 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem u_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φu Torus.b = (0 : ℤ) • Torus.c + (1 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of ((uM (s + 2))) (compat_u (s + 2) hm) 2 (0) (1) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_c (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.c = (1 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (0 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 0 (1) (0) (0) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_a (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.a = (0 : ℤ) • Torus.c + (0 : ℤ) • Torus.a + (1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 1 (0) (0) (1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

theorem rho_b (m : ℕ) (hm : 2 ≤ m) :
    (action m hm).φρ Torus.b = (-4 : ℤ) • Torus.c + (-1 : ℤ) • Torus.a + (-1 : ℤ) • Torus.b := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, (Nat.sub_add_cancel hm).symm⟩
  refine (matAct_gen_of (ρM) (compat_rho (s + 2) hm) 2 (-4) (-1) (-1) ?_ ?_ ?_).trans ?_ <;>
    first | (simp [-mul_eq_zero, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring1) | module

end Type310

end CFSG.CGT.Stroth77
