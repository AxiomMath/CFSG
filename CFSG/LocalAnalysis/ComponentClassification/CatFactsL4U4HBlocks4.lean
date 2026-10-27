module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks3

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace HBlocks

open Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryOut UnitaryConj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def bJ (x z : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, x, 0, 0; -x, 0, 0, 0; 0, 0, 0, z; 0, 0, -z, 0]

@[expose] def omg : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

@[expose] noncomputable def sfr (θ t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, -(θ / (t * (θ - h.bar θ))); θ, 0, 0, -(θ / (t * (θ - h.bar θ))) * h.bar θ;
    0, 1, θ / (t * (θ - h.bar θ)), 0; 0, -(h.bar θ)⁻¹, -(θ / (t * (θ - h.bar θ))) * θ⁻¹, 0]

@[expose] noncomputable def mk (κ l y : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; κ / y, 1, 0, κ * l / (y * h.bar y); -(κ * l), 0, 1, κ / h.bar y; 0, 0, 0, 1]

local macro "hb4_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (
    simp only [bJ, omg, sfr, mk, blk, X1, stdG, stdE, uStar, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.diagonal_apply, Matrix.smul_apply,
      Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, smul_eq_mul,
      map_zero, map_one, map_neg, map_add, map_sub, map_mul, map_div₀, map_inv₀, h.bar_bar,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, neg_zero, Fin.reduceEq,
      ite_true, ite_false, neg_mul, mul_neg, neg_neg] $[$loc]?))

omit [Field K] in
theorem transpose_mul_bJ_mul {R : Type*} [CommRing R] {D : Matrix (Fin 4) (Fin 4) R}
    (h02 : D 0 2 = 0) (h03 : D 0 3 = 0) (h12 : D 1 2 = 0) (h13 : D 1 3 = 0) (h20 : D 2 0 = 0)
    (h21 : D 2 1 = 0) (h30 : D 3 0 = 0) (h31 : D 3 1 = 0)
    (hu : D 0 0 * D 1 1 - D 0 1 * D 1 0 = 1) (hl : D 2 2 * D 3 3 - D 2 3 * D 3 2 = 1)
    (x z : R) :
    Dᵀ * !![0, x, 0, 0; -x, 0, 0, 0; 0, 0, 0, z; 0, 0, -z, 0] * D =
      !![0, x, 0, 0; -x, 0, 0, 0; 0, 0, 0, z; 0, 0, -z, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20, h21, h30, h31]
  all_goals first
    | ring1
    | linear_combination x * hu
    | linear_combination -(x * hu)
    | linear_combination z * hl
    | linear_combination -(z * hl)

theorem transpose_mul_bJ_mul' {D : Matrix (Fin 4) (Fin 4) K} (hD : IsBD D)
    (hu : (ul D).det = 1) (hl : (lr D).det = 1) (x z : K) : Dᵀ * bJ x z * D = bJ x z := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := hD
  rw [ul, Matrix.det_fin_two_of] at hu
  rw [lr, Matrix.det_fin_two_of] at hl
  exact transpose_mul_bJ_mul h02 h03 h12 h13 h20 h21 h30 h31 hu hl x z

theorem stdE_transpose_bJ (d x z : K) :
    (stdE h d)ᵀ * bJ x z * stdE h d = bJ (x * d) (z * (h.bar d)⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;> hb4_norm <;> ring

theorem uStar_sfr {θ t : K} (hθ : θ ≠ 0) (hθb : h.bar θ ≠ θ) (ht : h.bar t = -t) (ht0 : t ≠ 0) :
    uStar h (sfr h θ t) * omg * sfr h θ t = t⁻¹ • stdG := by
  have hθ' : h.bar θ ≠ 0 := fun h0 => hθ ((map_eq_zero h.bar).1 h0)
  have hd : θ - h.bar θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθb)
  have hd' : h.bar θ - θ ≠ 0 := sub_ne_zero.2 hθb
  ext i j
  fin_cases i <;> fin_cases j <;> hb4_norm <;> (try simp only [ht]) <;> field_simp <;> ring

theorem transpose_sfr {θ t : K} (hθ : θ ≠ 0) (hθb : h.bar θ ≠ θ) (ht0 : t ≠ 0) :
    (sfr h θ t)ᵀ * omg * sfr h θ t =
      bJ ((h.bar θ - θ) / h.bar θ) (θ / (t ^ 2 * (θ - h.bar θ))) := by
  have hθ' : h.bar θ ≠ 0 := fun h0 => hθ ((map_eq_zero h.bar).1 h0)
  have hd : θ - h.bar θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθb)
  ext i j
  fin_cases i <;> fin_cases j <;> hb4_norm <;> field_simp <;> ring

theorem det_bJ (x z : K) : (bJ x z).det = x ^ 2 * z ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [bJ, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem unitary_mk {κ l y : K} (hκ : κ + h.bar κ = 0) (hbl : h.bar l = l)
    (hy : y ≠ 0) : uStar h (mk h κ l y) * stdG * mk h κ l y = stdG := by
  have hy' : h.bar y ≠ 0 := fun h0 => hy ((map_eq_zero h.bar).1 h0)
  ext i j
  fin_cases i <;> fin_cases j <;> hb4_norm <;> (try simp only [hbl]) <;> field_simp <;>
    first
    | linear_combination hκ
    | linear_combination l * hκ
    | linear_combination (-l) * hκ

theorem det_mk (κ l y : K) : (mk h κ l y).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [mk, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem transpose_mk {κ l y : K} (hy : y ≠ 0) :
    (mk h κ l y)ᵀ * bJ y (h.bar y)⁻¹ * mk h κ l y = bJ y (h.bar y)⁻¹ := by
  have hy' : h.bar y ≠ 0 := fun h0 => hy ((map_eq_zero h.bar).1 h0)
  ext i j
  fin_cases i <;> fin_cases j <;> hb4_norm <;> field_simp <;> ring

theorem eq_zero_of_blk_mul_mk (h2 : (2 : K) ≠ 0) {κ l y x w : K} (hl0 : l ≠ 0)
    (hE : blk x 0 0 w * mk h κ l y = mk h κ l y * X1 l) : κ = 0 := by
  have e00 := congrFun (congrFun hE 0) 0
  have e22 := congrFun (congrFun hE 2) 2
  have e20 := congrFun (congrFun hE 2) 0
  hb4_norm at e00 e22 e20
  have hw : w = -l := by linear_combination e22
  rw [hw] at e20
  have : κ * (2 * l * l) = 0 := by linear_combination e20
  rcases mul_eq_zero.1 this with h0 | h0
  · exact h0
  · exact absurd h0 (mul_ne_zero (mul_ne_zero h2 hl0) hl0)

end HBlocks

end CFSG.ComponentClassification.CatFactsL4U4
