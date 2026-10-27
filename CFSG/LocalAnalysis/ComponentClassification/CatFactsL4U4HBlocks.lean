module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4ConjU4
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Core
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4U4Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace HBlocks

open Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryOut UnitaryConj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def X1 (l : K) : Matrix (Fin 4) (Fin 4) K :=
  !![l, 0, 0, 0; 0, l, 0, 0; 0, 0, -l, 0; 0, 0, 0, -l]

@[expose] noncomputable def U12 (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, c, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -h.bar c, 1]

@[expose] noncomputable def U21 (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; c, 1, 0, 0; 0, 0, 1, -h.bar c; 0, 0, 0, 1]

@[expose] noncomputable def Hd (d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![d, 0, 0, 0; 0, d⁻¹, 0, 0; 0, 0, (h.bar d)⁻¹, 0; 0, 0, 0, h.bar d]

@[expose] def Wm : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

@[expose] def blk (x b f y : K) : Matrix (Fin 4) (Fin 4) K :=
  !![x, 0, 0, b; 0, x, -b, 0; 0, f, y, 0; -f, 0, 0, y]

@[expose] def gfix (β γ : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, β, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, γ, 0, 1]

local macro "hblocks_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    simp only [U12, U21, Hd, Wm, X1, blk, gfix, stdG, uStar, Matrix.map_apply,
      Matrix.transpose_apply,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val,
      Matrix.neg_apply, Matrix.one_apply, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one,
      map_zero, map_one, map_neg, map_add, map_mul, h.bar_bar, mul_zero, zero_mul, mul_one,
      one_mul, add_zero, zero_add, neg_zero, Fin.reduceEq, ite_true, ite_false, neg_mul,
      mul_neg, neg_neg] $[$loc]?))

theorem U12_mul (c c' : K) : U12 h c * U12 h c' = U12 h (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> ring

theorem U21_mul (c c' : K) : U21 h c * U21 h c' = U21 h (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm
  all_goals ring

theorem U12_zero : U12 h (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm

theorem U21_zero : U21 h (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm

theorem unitary_U12 (c : K) : uStar h (U12 h c) * stdG * U12 h c = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> ring

theorem unitary_U21 (c : K) : uStar h (U21 h c) * stdG * U21 h c = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> ring

theorem unitary_Wm : uStar h (Wm : Matrix (Fin 4) (Fin 4) K) * stdG * Wm = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm

theorem unitary_Hd {d : K} (hd : d ≠ 0) : uStar h (Hd h d) * stdG * Hd h d = stdG := by
  have hb : h.bar d ≠ 0 := fun h0 => hd ((map_eq_zero h.bar).1 h0)
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> simp [map_inv₀, h.bar_bar, hd, hb]

theorem unitary_X1 {l : K} (hl : h.bar l * l = -1) :
    uStar h (X1 l) * stdG * X1 l = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> linear_combination -hl

theorem det_U12 (c : K) : (U12 h c).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [U12, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_U21 (c : K) : (U21 h c).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [U21, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_Wm : (Wm : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Wm, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_Hd {d : K} (hd : d ≠ 0) : (Hd h d).det = 1 := by
  have hb : h.bar d ≠ 0 := fun h0 => hd ((map_eq_zero h.bar).1 h0)
  rw [Matrix.det_succ_row_zero]
  simp [Hd, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  field_simp

theorem det_X1 {l : K} (hl : l ^ 2 = -1) : (X1 l).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [X1, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  linear_combination (l ^ 2 - 1) * hl

theorem U12_comm_X1 (c l : K) : U12 h c * X1 l = X1 l * U12 h c := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> ring

theorem U21_comm_X1 (c l : K) : U21 h c * X1 l = X1 l * U21 h c := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> ring

theorem Hd_comm_X1 (d l : K) : Hd h d * X1 l = X1 l * Hd h d := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> ring

theorem Wm_comm_X1 (l : K) : (Wm : Matrix (Fin 4) (Fin 4) K) * X1 l = X1 l * Wm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Wm, X1, Matrix.mul_apply, Fin.sum_univ_four]

theorem Hd_mul_Hd_inv {d : K} (hd : d ≠ 0) : Hd h d * Hd h d⁻¹ = 1 := by
  have hb : h.bar d ≠ 0 := fun h0 => hd ((map_eq_zero h.bar).1 h0)
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> simp [map_inv₀, hd, hb]

theorem Hd_conj_U12 {d : K} (hd : d ≠ 0) (c : K) :
    Hd h d * U12 h c * Hd h d⁻¹ = U12 h (d ^ 2 * c) := by
  have hb : h.bar d ≠ 0 := fun h0 => hd ((map_eq_zero h.bar).1 h0)
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> simp [map_inv₀, hd, hb] <;> field_simp

theorem Hd_conj_U21 {d : K} (hd : d ≠ 0) (c : K) :
    Hd h d * U21 h c * Hd h d⁻¹ = U21 h ((d⁻¹) ^ 2 * c) := by
  have hb : h.bar d ≠ 0 := fun h0 => hd ((map_eq_zero h.bar).1 h0)
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> simp [map_inv₀, hd, hb] <;> field_simp

theorem Wm_mul_Wm : (Wm : Matrix (Fin 4) (Fin 4) K) * Wm = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Wm, Matrix.mul_apply, Fin.sum_univ_four]

theorem commutator_Hd_Wm {l : K} (hl : l ^ 2 = -1) :
    Hd h l * Wm * Hd h l⁻¹ * (-Wm) = -1 := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl
  have hb : h.bar l ≠ 0 := fun h0 => hl0 ((map_eq_zero h.bar).1 h0)
  have hbl : h.bar l ^ 2 = -1 := by rw [← map_pow, hl, map_neg, map_one]
  have hli : l⁻¹ = -l := by
    field_simp
    linear_combination hl
  have hbli : (h.bar l)⁻¹ = -h.bar l := by
    field_simp
    linear_combination hbl
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;> simp [hli, hbli] <;>
    first | linear_combination hl | linear_combination -hl | linear_combination hbl

theorem U12_pow (c : K) (n : ℕ) : U12 h c ^ n = U12 h (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, U12_zero]
  | succ n ih => rw [pow_succ, ih, U12_mul, Nat.cast_succ, add_one_mul]

theorem U21_pow (c : K) (n : ℕ) : U21 h c ^ n = U21 h (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, U21_zero]
  | succ n ih => rw [pow_succ, ih, U21_mul, Nat.cast_succ, add_one_mul]

omit h in
theorem X1_eq_stdDl (l : K) : X1 l = stdDl l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, stdDl]

theorem eq_blk_of_comm {M : Matrix (Fin 4) (Fin 4) K} (h1 : M * U12 h 1 = U12 h 1 * M)
    (h2 : M * U21 h 1 = U21 h 1 * M) : M = blk (M 0 0) (M 0 3) (M 2 1) (M 2 2) := by
  have a00 := congrFun (congrFun h1 0) 0
  have a01 := congrFun (congrFun h1 0) 1
  have a02 := congrFun (congrFun h1 0) 2
  have a03 := congrFun (congrFun h1 0) 3
  have a21 := congrFun (congrFun h1 2) 1
  have a22 := congrFun (congrFun h1 2) 2
  have a31 := congrFun (congrFun h1 3) 1
  have a32 := congrFun (congrFun h1 3) 2
  have b00 := congrFun (congrFun h2 0) 0
  have b03 := congrFun (congrFun h2 0) 3
  have b21 := congrFun (congrFun h2 2) 1
  have b22 := congrFun (congrFun h2 2) 2
  hblocks_norm at a00 a01 a02 a03 a21 a22 a31 a32 b00 b03 b21 b22
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;>
    first
    | rfl
    | linear_combination a00 | linear_combination -a00
    | linear_combination a01 | linear_combination -a01
    | linear_combination a02 | linear_combination -a02
    | linear_combination a03 | linear_combination -a03
    | linear_combination a21 | linear_combination -a21
    | linear_combination a22 | linear_combination -a22
    | linear_combination a31 | linear_combination -a31
    | linear_combination a32 | linear_combination -a32
    | linear_combination b00 | linear_combination -b00
    | linear_combination b03 | linear_combination -b03
    | linear_combination b21 | linear_combination -b21
    | linear_combination b22

theorem blk_rel {x b f y ν μ : K} (hE : blk x b f y * U12 h ν = U12 h μ * blk x b f y) :
    x * (ν - μ) = 0 ∧ b * (h.bar ν - μ) = 0 ∧ f * (ν - h.bar μ) = 0 ∧
      y * (h.bar ν - h.bar μ) = 0 := by
  have e01 := congrFun (congrFun hE 0) 1
  have e02 := congrFun (congrFun hE 0) 2
  have e31 := congrFun (congrFun hE 3) 1
  have e32 := congrFun (congrFun hE 3) 2
  hblocks_norm at e01 e02 e31 e32
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination e01
  · linear_combination -e02
  · linear_combination -e31
  · linear_combination -e32

theorem blk_unitary {x b f y : K} (hU : uStar h (blk x b f y) * stdG * blk x b f y = stdG) :
    b * h.bar f + h.bar x * y = 1 := by
  have e := congrFun (congrFun hU 0) 2
  hblocks_norm at e
  linear_combination e

theorem unitary_gfix {β γ : K} (hβ : β + h.bar β = 0) (hγ : γ + h.bar γ = 0) :
    uStar h (gfix β γ) * stdG * gfix β γ = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;>
    first | rfl | linear_combination hβ | linear_combination hγ

omit h in
theorem det_gfix (β γ : K) : (gfix β γ).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [gfix, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem map_gfix (β γ : K) : (gfix β γ).map h.bar = gfix (h.bar β) (h.bar γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm

theorem blk_mul_gfix {β γ b f : K} (h1 : b * h.bar γ = β * f) (h2 : b * γ = h.bar β * f) :
    blk 0 b f 0 * gfix (h.bar β) (h.bar γ) = gfix β γ * blk 0 b f 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> hblocks_norm <;>
    first | rfl | linear_combination h1 | linear_combination h2

theorem eq_zero_of_blk_mul_gfix (h2 : (2 : K) ≠ 0) {l x y β γ : K} (hl : l ≠ 0)
    (hE : blk x 0 0 y * gfix β γ = gfix β γ * X1 l) : β = 0 := by
  have e00 := congrFun (congrFun hE 0) 0
  have e02 := congrFun (congrFun hE 0) 2
  simp only [blk, gfix, X1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val, mul_zero, mul_one, one_mul,
    add_zero, zero_add] at e00 e02
  have hx : x = l := by linear_combination e00
  rw [hx] at e02
  have : (2 * l) * β = 0 := by linear_combination e02
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (mul_ne_zero h2 hl)
  · exact h0

theorem map_U12 (φ : K →+* K) (hφ : ∀ c, φ (h.bar c) = h.bar (φ c)) (c : K) :
    (U12 h c).map φ = U12 h (φ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U12, hφ]

theorem map_U21 (φ : K →+* K) (hφ : ∀ c, φ (h.bar c) = h.bar (φ c)) (c : K) :
    (U21 h c).map φ = U21 h (φ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [U21, hφ]

omit h in
theorem map_gfix' (φ : K →+* K) (β γ : K) : (gfix β γ).map φ = gfix (φ β) (φ γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gfix]

theorem trace_U12 (c : K) : (U12 h c).trace = 4 := by
  simp only [U12, Matrix.trace, Matrix.diag, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val]
  norm_num

theorem trace_U21 (c : K) : (U21 h c).trace = 4 := by
  simp only [U21, Matrix.trace, Matrix.diag, Fin.sum_univ_four, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val]
  norm_num

omit h in
theorem blk_one : blk (1 : K) 0 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

omit h in
theorem blk_mul_blk (x y x' y' : K) :
    blk x 0 0 y * blk x' 0 0 y' = blk (x * x') 0 0 (y * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_four]

omit h in
theorem det_blk (x y : K) : (blk x 0 0 y).det = x ^ 2 * y ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [blk, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

omit h in
theorem stdG_map (φ : K →+* K) : (stdG : Matrix (Fin 4) (Fin 4) K).map φ = stdG := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdG]

theorem uStar_map (φ : K →+* K) (hφ : ∀ c, φ (h.bar c) = h.bar (φ c))
    (M : Matrix (Fin 4) (Fin 4) K) : uStar h (M.map φ) = (uStar h M).map φ := by
  ext i j
  simp [uStar, hφ]

end HBlocks

end CFSG.ComponentClassification.CatFactsL4U4
