module

public import CFSG.CGT.Stroth77.SigmaFour
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Type321

@[expose] def k : Fin 3 → ℕ := ![3, 3, 3]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![4, -1, -1]

@[expose] def uvA : Fin 3 → ℤ := ![4, 1, 6]

@[expose] def tM : IntMat :=
  ofCols ![1, 1, 2] ![0, 3, 0] (ρM *ᵥ uvA)

@[expose] def uvM : IntMat :=
  ofCols ![-3, 1, -1] uvA (ρM *ᵥ (tM *ᵥ uvA))

@[expose] def uM : IntMat := uMat ![-1, 0, 0] 0

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv : Compat k uvM :=
  Compat.of_witness (C := uvM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem compat_t : Compat k tM :=
  Compat.of_witness (C := tM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem compat_u : Compat k uM :=
  Compat.of_witness (C := uM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem compat_rho : Compat k ρM :=
  Compat.of_witness (C := ρM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem uv_sq : MatEq k (uvM * uvM) (1) :=
  MatEq.of_witness (W := !![-9, 62, -94; -3, 17, -6; 2, -5, 12]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem t_sq : MatEq k (tM * tM) (1) :=
  MatEq.of_witness (W := !![7, 0, -14; -1, 1, 5; -1, 0, 10]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem uv_comm_t : MatEq k (tM * uvM) (uvM * tM) :=
  MatEq.of_witness (W := !![-25, 20, 52; -5, -4, 35; 1, -5, 29]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem rho_cube : MatEq k (ρM * (ρM * ρM)) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem u_sq : MatEq k (uM * uM) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem u_rho : MatEq k (ρM * (uM * (ρM * uM))) (1) :=
  MatEq.of_witness (W := !![0, -1, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem uv_rho : MatEq k (ρM * uvM) (tM * ρM) :=
  MatEq.of_witness (W := !![-1, 0, 10; 0, 0, 0; 0, 0, 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem t_rho : MatEq k (ρM * tM) (tM * (uvM * ρM)) :=
  MatEq.of_witness (W := !![5, 14, 24; -1, -24, 18; 0, -25, 23]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem uv_comm_u : MatEq k (uM * uvM) (uvM * uM) :=
  MatEq.of_witness (W := !![0, -11, -11; 0, -2, -1; 0, 1, 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem t_u : MatEq k (uM * tM) (tM * (uvM * uM)) :=
  MatEq.of_witness (W := !![-4, 14, -25; 1, -24, 3; 0, -25, 2]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

@[expose] def action : SigmaFourAction k :=
  SigmaFourAction.ofMatEq uvM tM uM ρM
    compat_uv compat_t compat_u compat_rho
    uv_sq t_sq uv_comm_t rho_cube u_sq u_rho uv_rho t_rho uv_comm_u t_u

end Type321

namespace Type331

@[expose] def k : Fin 3 → ℕ := ![3, 3, 3]

@[expose] def ρM : IntMat :=
  ofCols ![1, 0, 0] ![0, 0, 1] ![4, -1, -1]

@[expose] def uvA : Fin 3 → ℤ := ![4, 1, 6]

@[expose] def tM : IntMat :=
  ofCols ![1, 1, -2] ![0, 3, 0] (ρM *ᵥ uvA)

@[expose] def uvM : IntMat :=
  ofCols ![-3, 5, -1] uvA (ρM *ᵥ (tM *ᵥ uvA))

@[expose] def uM : IntMat := uMat ![3, 0, 0] 0

attribute [local simp] ρM uvA tM uvM uM uMat ofCols_apply Matrix.mul_apply
  Fin.sum_univ_three Matrix.mulVec dotProduct Matrix.one_apply k

theorem compat_uv : Compat k uvM :=
  Compat.of_witness (C := uvM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem compat_t : Compat k tM :=
  Compat.of_witness (C := tM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem compat_u : Compat k uM :=
  Compat.of_witness (C := uM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem compat_rho : Compat k ρM :=
  Compat.of_witness (C := ρM) (by intro i j; fin_cases i <;> fin_cases j <;> simp [k])

theorem uv_sq : MatEq k (uvM * uvM) (1) :=
  MatEq.of_witness (W := !![1, 14, 34; -6, 31, 60; 3, 7, 36]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem t_sq : MatEq k (tM * tM) (1) :=
  MatEq.of_witness (W := !![-7, 0, -14; 2, 1, 5; 1, 0, -4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem uv_comm_t : MatEq k (tM * uvM) (uvM * tM) :=
  MatEq.of_witness (W := !![1, 20, 60; 11, -4, 17; 3, -7, 3]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem rho_cube : MatEq k (ρM * (ρM * ρM)) (1) :=
  MatEq.of_witness (W := 0) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem u_sq : MatEq k (uM * uM) (1) :=
  MatEq.of_witness (W := !![1, 0, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem u_rho : MatEq k (ρM * (uM * (ρM * uM))) (1) :=
  MatEq.of_witness (W := !![1, 1, 0; 0, 0, 0; 0, 0, 0]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem uv_rho : MatEq k (ρM * uvM) (tM * ρM) :=
  MatEq.of_witness (W := !![-1, 0, 10; 0, 0, -2; 1, 0, 4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem t_rho : MatEq k (ρM * tM) (tM * (uvM * ρM)) :=
  MatEq.of_witness (W := !![3, -34, 72; -2, -10, -2; -1, 11, -21]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem uv_comm_u : MatEq k (uM * uvM) (uvM * uM) :=
  MatEq.of_witness (W := !![0, -1, 7; -2, -4, 1; 1, -1, 4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

theorem t_u : MatEq k (uM * tM) (tM * (uvM * uM)) :=
  MatEq.of_witness (W := !![12, -34, -11; -7, -10, 3; -4, 11, 4]) (by
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> ring1)

@[expose] def action : SigmaFourAction k :=
  SigmaFourAction.ofMatEq uvM tM uM ρM
    compat_uv compat_t compat_u compat_rho
    uv_sq t_sq uv_comm_t rho_cube u_sq u_rho uv_rho t_rho uv_comm_u t_u

end Type331

end CFSG.CGT.Stroth77
