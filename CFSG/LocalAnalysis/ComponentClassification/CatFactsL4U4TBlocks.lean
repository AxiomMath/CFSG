module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace TBlocks

open Matrix HBlocks

variable {F : Type} [Field F]

@[expose] def bd (a b : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![a 0 0, a 0 1, 0, 0; a 1 0, a 1 1, 0, 0; 0, 0, b 0 0, b 0 1; 0, 0, b 1 0, b 1 1]

@[expose] def uu (c : F) : Matrix (Fin 2) (Fin 2) F := !![1, c; 0, 1]

@[expose] def ll (c : F) : Matrix (Fin 2) (Fin 2) F := !![1, 0; c, 1]

@[expose] def jj : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

theorem bd_mul (a b a' b' : Matrix (Fin 2) (Fin 2) F) : bd a b * bd a' b' = bd (a * a') (b * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bd, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem bd_one : bd (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem det_bd (a b : Matrix (Fin 2) (Fin 2) F) : (bd a b).det = a.det * b.det := by
  rw [Matrix.det_succ_row_zero, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [bd, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem transpose_bd (a b : Matrix (Fin 2) (Fin 2) F) : (bd a b)ᵀ = bd aᵀ bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem map_bd {L : Type} [Field L] (φ : F →+* L) (a b : Matrix (Fin 2) (Fin 2) F) :
    (bd a b).map φ = bd (a.map φ) (b.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem isBD_bd (a b : Matrix (Fin 2) (Fin 2) F) : IsBD (bd a b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [bd]

theorem ul_bd (a b : Matrix (Fin 2) (Fin 2) F) : ul (bd a b) = a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ul, bd]

theorem lr_bd (a b : Matrix (Fin 2) (Fin 2) F) : lr (bd a b) = b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lr, bd]

theorem eq_bd {M : Matrix (Fin 4) (Fin 4) F} (hM : IsBD M) : M = bd (ul M) (lr M) := by
  obtain ⟨m02, m03, m12, m13, m20, m21, m30, m31⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, ul, lr, m02, m03, m12, m13, m20, m21, m30, m31]

theorem X1_eq_bd (l : F) : X1 l = bd (l • 1) ((-l) • 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, bd]

theorem bd_comm_X1 (a b : Matrix (Fin 2) (Fin 2) F) (l : F) : bd a b * X1 l = X1 l * bd a b := by
  rw [X1_eq_bd, bd_mul, bd_mul]
  simp

theorem trace_bd (a b : Matrix (Fin 2) (Fin 2) F) : (bd a b).trace = a.trace + b.trace := by
  simp [bd, Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem det_uu (c : F) : (uu c).det = 1 := by simp [uu, Matrix.det_fin_two]

theorem det_ll (c : F) : (ll c).det = 1 := by simp [ll, Matrix.det_fin_two]

theorem trace_uu (c : F) : (uu c).trace = 2 := by
  simp [uu, Matrix.trace, Fin.sum_univ_two]
  norm_num

theorem trace_ll (c : F) : (ll c).trace = 2 := by
  simp [ll, Matrix.trace, Fin.sum_univ_two]
  norm_num

theorem bd_eq_bJ (x y : F) : bd (x • jj) (y • jj) = bJ x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, jj, bJ]

theorem transpose_bJ (x y : F) : (bJ x y)ᵀ = -bJ x y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bJ]

local macro "tb_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    simp only [bd, uu, ll, jj, bJ, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.one_apply_eq,
      Matrix.one_apply_ne, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, ne_eq,
      Fin.reduceEq, not_false_eq_true, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      neg_zero, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply] $[$loc]?))

theorem eq_of_comm_bd {M : Matrix (Fin 4) (Fin 4) F}
    (h1 : M * bd (uu 1) 1 = bd (uu 1) 1 * M) (h2 : M * bd (ll 1) 1 = bd (ll 1) 1 * M)
    (h3 : M * bd 1 (uu 1) = bd 1 (uu 1) * M) (h4 : M * bd 1 (ll 1) = bd 1 (ll 1) * M) :
    M = bd (M 0 0 • 1) (M 2 2 • 1) := by
  have e : ∀ (N : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4), M * N = N * M →
      (M * N) i j = (N * M) i j := fun N i j hN => by rw [hN]
  have a1 := e _ 1 1 h1
  have a2 := e _ 2 1 h1
  have a3 := e _ 3 1 h1
  have a4 := e _ 0 2 h1
  have a5 := e _ 0 3 h1
  have a6 := e _ 0 1 h1
  have b1 := e _ 0 0 h2
  have b2 := e _ 2 0 h2
  have b3 := e _ 3 0 h2
  have c1 := e _ 0 3 h3
  have c2 := e _ 3 3 h3
  have c3 := e _ 2 3 h3
  have d1 := e _ 0 2 h4
  have d2 := e _ 2 2 h4
  have d3 := e _ 1 2 h4
  have d4 := e _ 3 2 h4
  tb_norm at a1 a2 a3 a4 a5 a6 b1 b2 b3
  tb_norm at c1 c2 c3 d1 d2 d3 d4
  ext i j
  fin_cases i <;> fin_cases j <;> tb_norm
  all_goals first
    | linear_combination a1
    | linear_combination -a1
    | linear_combination a2
    | linear_combination -a2
    | linear_combination a3
    | linear_combination -a3
    | linear_combination a4
    | linear_combination -a4
    | linear_combination a5
    | linear_combination -a5
    | linear_combination a6
    | linear_combination -a6
    | linear_combination b1
    | linear_combination -b1
    | linear_combination b2
    | linear_combination -b2
    | linear_combination b3
    | linear_combination -b3
    | linear_combination c1
    | linear_combination -c1
    | linear_combination c2
    | linear_combination -c2
    | linear_combination c3
    | linear_combination -c3
    | linear_combination d1
    | linear_combination -d1
    | linear_combination d2

theorem eq_of_inv_bd {M : Matrix (Fin 4) (Fin 4) F}
    (h1 : bd (uu 1) 1 * M * (bd (uu 1) 1)ᵀ = M) (h2 : bd (ll 1) 1 * M * (bd (ll 1) 1)ᵀ = M)
    (h3 : bd 1 (uu 1) * M * (bd 1 (uu 1))ᵀ = M) (h4 : bd 1 (ll 1) * M * (bd 1 (ll 1))ᵀ = M) :
    M = bJ (M 0 1) (M 2 3) := by
  have e : ∀ (N : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4), N * M * Nᵀ = M →
      (N * M * Nᵀ) i j = M i j := fun N i j hN => by rw [hN]
  have a := fun i j => e _ i j h1
  have b := fun i j => e _ i j h2
  have c := fun i j => e _ i j h3
  have d := fun i j => e _ i j h4
  have a00 := a 0 0
  have a02 := a 0 2
  have a03 := a 0 3
  have a20 := a 2 0
  have a30 := a 3 0
  have a01 := a 0 1
  have b11 := b 1 1
  have b12 := b 1 2
  have b13 := b 1 3
  have b21 := b 2 1
  have b31 := b 3 1
  have b10 := b 1 0
  have c22 := c 2 2
  have c23 := c 2 3
  have c20 := c 2 0
  have c21 := c 2 1
  have d33 := d 3 3
  have d32 := d 3 2
  tb_norm at a00 a02 a03 a20 a30 a01
  tb_norm at b11 b12 b13 b21 b31 b10
  tb_norm at c22 c23 c20 c21 d33 d32
  ext i j
  fin_cases i <;> fin_cases j <;> tb_norm
  all_goals first
    | linear_combination a00
    | linear_combination -a00
    | linear_combination a02
    | linear_combination -a02
    | linear_combination a03
    | linear_combination -a03
    | linear_combination a20
    | linear_combination -a20
    | linear_combination a30
    | linear_combination -a30
    | linear_combination a01
    | linear_combination -a01
    | linear_combination b11
    | linear_combination -b11
    | linear_combination b12
    | linear_combination -b12
    | linear_combination b13
    | linear_combination -b13
    | linear_combination b21
    | linear_combination -b21
    | linear_combination b31
    | linear_combination -b31
    | linear_combination b10
    | linear_combination -b10
    | linear_combination c22
    | linear_combination -c22
    | linear_combination c23
    | linear_combination -c23
    | linear_combination c20
    | linear_combination -c20
    | linear_combination c21
    | linear_combination -c21
    | linear_combination d33
    | linear_combination -d33
    | linear_combination d32
    | linear_combination -d32
    | linear_combination a00 - a01
    | linear_combination a01 - a00
    | linear_combination c22 - c23

end TBlocks

end CFSG.ComponentClassification.CatFactsL4U4
