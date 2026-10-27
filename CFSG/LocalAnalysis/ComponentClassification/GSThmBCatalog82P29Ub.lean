module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsL4U4
  UnitaryOut UnitaryConj HBlocks

namespace U4M

variable {K : Type} [Field K]

local macro "entry_close" h:ident a:ident b:ident c:ident : tactic => `(tactic|
  first
  | ring1
  | linear_combination ($h)
  | linear_combination (-$h)
  | linear_combination ($a) * $h
  | linear_combination (-$a) * $h
  | linear_combination ($b) * $h
  | linear_combination (-$b) * $h
  | linear_combination ($c) * $h
  | linear_combination (-$c) * $h)

@[expose] def dg (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![a, 0, 0, 0; 0, b, 0, 0; 0, 0, c, 0; 0, 0, 0, d]

theorem dg_mul_dg (a b c d a' b' c' d' : K) :
    dg a b c d * dg a' b' c' d' = dg (a * a') (b * b') (c * c') (d * d') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_four]

theorem dg_one : dg (1 : K) 1 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem dg_neg (a b c d : K) : dg (-a) (-b) (-c) (-d) = -dg a b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem dg_pow (a b c d : K) (j : ℕ) : dg a b c d ^ j = dg (a ^ j) (b ^ j) (c ^ j) (d ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero, pow_zero, pow_zero, pow_zero, dg_one]
  | succ j ih => rw [pow_succ, ih, dg_mul_dg, ← pow_succ, ← pow_succ, ← pow_succ, ← pow_succ]

theorem det_dg (a b c d : K) : (dg a b c d).det = a * b * c * d := by
  rw [dg, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem X1_eq_dg (l : K) : X1 l = dg l l (-l) (-l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, dg]

theorem blk_eq_dg (x y : K) : blk x 0 0 y = dg x x y y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, dg]

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem unitary_dg {a b c d : K} (hac : h.bar a * c = 1) (hbd : h.bar b * d = 1) :
    uStar h (dg a b c d) * stdG * dg a b c d = stdG := by
  have hca : h.bar c * a = 1 := by
    have := congrArg h.bar hac
    rw [map_mul, h.bar_bar, map_one] at this
    rw [mul_comm]
    exact this
  have hdb : h.bar d * b = 1 := by
    have := congrArg h.bar hbd
    rw [map_mul, h.bar_bar, map_one] at this
    rw [mul_comm]
    exact this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, stdG, uStar, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, hac, hbd,
      hca, hdb]

variable (z w : K)

@[expose] def aH : Matrix (Fin 4) (Fin 4) K := dg z w (-w) (-z)

@[expose] def apH : Matrix (Fin 4) (Fin 4) K := dg z (-z) (-w) w

@[expose] def tH : Matrix (Fin 4) (Fin 4) K := !![1, 0, 0, 0; 0, 0, 0, -w; 0, 0, 1, 0; 0, z, 0, 0]

@[expose] def tiH : Matrix (Fin 4) (Fin 4) K := !![1, 0, 0, 0; 0, 0, 0, w; 0, 0, 1, 0; 0, -z, 0, 0]

@[expose] def wpH : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, -w; 0, 0, -w, 0; 0, z, 0, 0; z, 0, 0, 0]

@[expose] def kH (l : K) : Matrix (Fin 4) (Fin 4) K := dg l (-l) (-l) l

variable {z w}

theorem tH_mul_tiH (hzw : z * w = 1) : tH z w * tiH z w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tH, tiH, Matrix.mul_apply, Fin.sum_univ_four] <;>
    entry_close hzw z w z

theorem tiH_aH_tH (hzw : z * w = 1) : tiH z w * aH z w * tH z w = apH z w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tH, tiH, aH, apH, dg, Matrix.mul_apply, Fin.sum_univ_four] <;> entry_close hzw z w z

theorem tiH_Wm_tH : tiH z w * Wm * tH z w = wpH z w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tH, tiH, Wm, wpH, Matrix.mul_apply, Fin.sum_univ_four]

theorem apH_aH : apH z w * aH z w = aH z w * apH z w := by
  rw [apH, aH, dg_mul_dg, dg_mul_dg]
  congr 1 <;> ring

theorem aH_wpH : aH z w * wpH z w = -(wpH z w * aH z w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aH, wpH, dg, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem Wm_apH : Wm * apH z w = -(apH z w * Wm) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [apH, Wm, dg, Matrix.mul_apply, Fin.sum_univ_four]

theorem Wm_wpH : Wm * wpH z w = -(wpH z w * Wm) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wpH, Wm, Matrix.mul_apply, Fin.sum_univ_four]

theorem Wm_aH_Wm_aH (hzw : z * w = 1) : Wm * aH z w * Wm * aH z w = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aH, Wm, dg, Matrix.mul_apply, Fin.sum_univ_four] <;>
    entry_close hzw z w z

theorem tiH_kH_tH (hzw : z * w = 1) (l : K) : tiH z w * kH l * tH z w = X1 l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tH, tiH, kH, X1, dg, Matrix.mul_apply, Fin.sum_univ_four] <;> entry_close hzw z w l

theorem tH_mul_tH (hzw : z * w = 1) : tH z w * tH z w = dg 1 (-1) 1 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tH, dg, Matrix.mul_apply, Fin.sum_univ_four] <;>
    entry_close hzw z w z

theorem X1_kH {l : K} (hl : l ^ 2 = -1) : X1 l * kH l = dg (-1) 1 (-1) 1 := by
  rw [X1_eq_dg, kH, dg_mul_dg]
  congr 1 <;> first | linear_combination hl | linear_combination -hl

theorem tH_sq_eq (hzw : z * w = 1) {l : K} (hl : l ^ 2 = -1) :
    tH z w * tH z w = -(X1 l * kH l) := by
  rw [tH_mul_tH hzw, X1_kH hl, ← dg_neg, neg_neg]

theorem kH_apH (l : K) : kH l * apH z w = blk (l * z) 0 0 (l * w) := by
  rw [kH, apH, dg_mul_dg, blk_eq_dg]
  congr 1 <;> ring

theorem X1_kH_sq {l : K} (hl : l ^ 2 = -1) : X1 l * kH l * (X1 l * kH l) = 1 := by
  rw [X1_kH hl, dg_mul_dg, ← dg_one]
  congr 1 <;> ring

theorem kH_mul_kH {l : K} (hl : l ^ 2 = -1) : kH l * kH l = -1 := by
  rw [kH, dg_mul_dg, ← dg_one, ← dg_neg]
  congr 1 <;> linear_combination hl

theorem X1_mul_X1 {l : K} (hl : l ^ 2 = -1) : X1 l * X1 l = -1 := by
  rw [X1_eq_dg, dg_mul_dg, ← dg_one, ← dg_neg]
  congr 1 <;> linear_combination hl

theorem X1_wpH_apply (l : K) : (X1 l * wpH z w) 0 3 = -(l * w) := by
  simp [X1, wpH, Matrix.mul_apply, Fin.sum_univ_four]

theorem Wm_mul_dg_apply (a b c d : K) : (Wm * dg a b c d : Matrix (Fin 4) (Fin 4) K) 0 0 = 0 := by
  simp [Wm, dg, Matrix.mul_apply, Fin.sum_univ_four]

theorem unitary_aH (hzw : z * w = 1) (hbz : h.bar z = -z) (hbw : h.bar w = -w) :
    uStar h (aH z w) * stdG * aH z w = stdG :=
  unitary_dg h (by rw [hbz]; linear_combination hzw) (by rw [hbw]; linear_combination hzw)

theorem det_aH (hzw : z * w = 1) : (aH z w).det = 1 := by
  rw [aH, det_dg]
  linear_combination (z * w + 1) * hzw

theorem unitary_kH {l : K} (hbl : h.bar l = l) (hl : l ^ 2 = -1) :
    uStar h (kH l) * stdG * kH l = stdG :=
  unitary_dg h (by rw [hbl]; linear_combination -hl) (by rw [map_neg, hbl]; linear_combination -hl)

theorem det_kH {l : K} (hl : l ^ 2 = -1) : (kH l).det = 1 := by
  rw [kH, det_dg]
  linear_combination (l ^ 2 - 1) * hl

theorem unitary_tH (hzw : z * w = 1) (hbz : h.bar z = -z) (hbw : h.bar w = -w) :
    uStar h (tH z w) * stdG * tH z w = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tH, stdG, uStar, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, hbz,
      hbw] <;> entry_close hzw z w z

theorem det_tH (hzw : z * w = 1) : (tH z w).det = 1 := by
  rw [tH, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  entry_close hzw z w z

theorem Wm_eq_U : (Wm : Matrix (Fin 4) (Fin 4) K) = U12 h 1 * U21 h (-1) * U12 h 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Wm, U12, U21, Matrix.mul_apply, Fin.sum_univ_four]

theorem aH_Wm (hzw : z * w = 1) (hbz : h.bar z = -z) (hbw : h.bar w = -w) :
    aH z w * Wm = U12 h z * U21 h (-w) * U12 h z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aH, dg, Wm, U12, U21, Matrix.mul_apply, Fin.sum_univ_four, hbz, hbw, -mul_eq_zero] <;>
    entry_close hzw z w z

end U4M

end CFSG.ComponentClassification.GSThmB.P29
