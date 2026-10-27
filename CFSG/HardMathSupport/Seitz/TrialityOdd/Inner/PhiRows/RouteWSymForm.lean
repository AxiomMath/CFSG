module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWSym2
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Matrix Polynomial

variable {k : Type*} [Field k]

def SymCongr (A B : Matrix (Fin 3) (Fin 3) k) : Prop :=
  ∃ P : Matrix (Fin 3) (Fin 3) k, IsUnit P.det ∧ A = P * B * Pᵀ

theorem SymCongr.symm {A B : Matrix (Fin 3) (Fin 3) k} (h : SymCongr A B) : SymCongr B A := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P⁻¹, (Matrix.isUnit_nonsing_inv_det_iff).2 hP, ?_⟩
  rw [Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.det_transpose P).symm ▸ hP), Matrix.mul_one]

theorem SymCongr.trans {A B C : Matrix (Fin 3) (Fin 3) k} (h₁ : SymCongr A B)
    (h₂ : SymCongr B C) : SymCongr A C := by
  obtain ⟨P, hP, rfl⟩ := h₁
  obtain ⟨Q, hQ, rfl⟩ := h₂
  refine ⟨P * Q, by rw [Matrix.det_mul]; exact hP.mul hQ, ?_⟩
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem exists_sq_add_sq_eq_one [Finite k] (h2 : (2 : k) ≠ 0) {a b : k} (ha : a ≠ 0)
    (hb : b ≠ 0) : ∃ x y : k, a * x ^ 2 + b * y ^ 2 = 1 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hchar : ringChar k ≠ 2 := by
    intro h
    apply h2
    have := ringChar.spec k 2
    exact (this.2 (by rw [h])).symm ▸ (by simp)
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  have hf : degree (C a * X ^ 2) = 2 := by
    rw [degree_C_mul_X_pow 2 ha]; rfl
  have hg : degree (C b * X ^ 2 - 1 : k[X]) = 2 := by
    rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_C_mul_X_pow 2 hb]
    · rfl
    · rw [degree_one]; exact compareOfLessAndEq_eq_lt.mp rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨x, y, ?_⟩
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one] at hxy
  linear_combination hxy

theorem symCongr_diag_first {a b c x y : k} (h : a * x ^ 2 + b * y ^ 2 = 1) :
    SymCongr (diagonal ![1, a * b, c]) (diagonal ![a, b, c]) := by
  refine ⟨!![x, y, 0; -(b * y), a * x, 0; 0, 0, 1], ?_, ?_⟩
  · have hd : (!![x, y, 0; -(b * y), a * x, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) k).det = 1 := by
      rw [Matrix.det_fin_three]
      simp
      linear_combination h
    rw [hd]; exact isUnit_one
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.vecMul,
        dotProduct] <;>
      first | ring1 | (linear_combination h) | (linear_combination (-1 : k) * h) |
        (linear_combination (a * b) * h) | (linear_combination (-(a * b)) * h)

theorem symCongr_diag_second {u b c x y : k} (h : b * x ^ 2 + c * y ^ 2 = 1) :
    SymCongr (diagonal ![u, 1, b * c]) (diagonal ![u, b, c]) := by
  refine ⟨!![1, 0, 0; 0, x, y; 0, -(c * y), b * x], ?_, ?_⟩
  · have hd : (!![1, 0, 0; 0, x, y; 0, -(c * y), b * x] : Matrix (Fin 3) (Fin 3) k).det = 1 := by
      rw [Matrix.det_fin_three]
      simp
      linear_combination h
    rw [hd]; exact isUnit_one
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.vecMul,
        dotProduct] <;>
      first | ring1 | (linear_combination h) | (linear_combination (-1 : k) * h) |
        (linear_combination (b * c) * h) | (linear_combination (-(b * c)) * h)

theorem symCongr_diag_one_one [Finite k] (h2 : (2 : k) ≠ 0) {a b c : k} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) : SymCongr (diagonal ![a, b, c]) (diagonal ![1, 1, a * b * c]) := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_eq_one h2 ha hb
  obtain ⟨x', y', hxy'⟩ := exists_sq_add_sq_eq_one h2 (mul_ne_zero ha hb) hc
  exact ((symCongr_diag_second (u := 1) hxy').trans (symCongr_diag_first hxy)).symm

theorem symCongr_smul_sym2Form (h2 : (2 : k) ≠ 0) (c : k) :
    SymCongr (diagonal ![c, -2 * c, -c]) (c • sym2Form k) := by
  refine ⟨!![1, 0, 2⁻¹; 0, 1, 0; 1, 0, -2⁻¹], ?_, ?_⟩
  · have hd : (!![1, 0, 2⁻¹; 0, 1, 0; 1, 0, -2⁻¹] : Matrix (Fin 3) (Fin 3) k).det = -1 := by
      rw [Matrix.det_fin_three]
      simp
      field_simp
      ring
    rw [hd]; exact isUnit_one.neg
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sym2Form, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> ring

theorem symCongr_diag_scale {d l : k} (hl : l ≠ 0) :
    SymCongr (diagonal ![1, 1, d * l ^ 2]) (diagonal ![1, 1, d]) := by
  refine ⟨diagonal ![1, 1, l], ?_, ?_⟩
  · rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using hl
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

theorem exists_symCongr_diagonal (h2 : (2 : k) ≠ 0) (B : Matrix (Fin 3) (Fin 3) k) (hB : Bᵀ = B) :
    ∃ a : Fin 3 → k, SymCongr B (diagonal a) := by
  classical
  have : Invertible (2 : k) := invertibleOfNonzero h2
  have hsymm : (Matrix.toBilin' B).IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.2 hB
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 hsymm)
  set v' := v.reindex (finCongr (Module.finrank_fin_fun k)) with hv'
  have hv'o : ∀ i j, i ≠ j → Matrix.toBilin' B (v' i) (v' j) = 0 := by
    intro i j hij
    simp only [hv', Module.Basis.reindex_apply]
    exact hv (fun h => hij ((finCongr (Module.finrank_fin_fun k)).symm.injective h))
  set Pm := (Pi.basisFun k (Fin 3)).toMatrix v' with hPm
  have hdiag : Pmᵀ * B * Pm = diagonal fun i => Matrix.toBilin' B (v' i) (v' i) := by
    have h := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := Pi.basisFun k (Fin 3)) v'
      (Matrix.toBilin' B)
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h
    rw [h]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · exact hv'o i j hij
  have hPu : IsUnit Pm.det := by
    have := (Pi.basisFun k (Fin 3)).invertibleToMatrix v'
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨fun i => Matrix.toBilin' B (v' i) (v' i), ?_⟩
  refine SymCongr.symm ⟨Pmᵀ, by rw [Matrix.det_transpose]; exact hPu, ?_⟩
  rw [Matrix.transpose_transpose, hdiag]

theorem exists_sym_form_equiv [Finite k] (h2 : (2 : k) ≠ 0)
    (B : Matrix (Fin 3) (Fin 3) k) (hB : Bᵀ = B) (hdet : B.det ≠ 0) :
    ∃ (P : GL (Fin 3) k) (c : kˣ),
      B = (c : k) • ((P : Matrix (Fin 3) (Fin 3) k) * sym2Form k * (P : Matrix (Fin 3) (Fin 3) k)ᵀ) := by
  obtain ⟨a, hBa⟩ := exists_symCongr_diagonal h2 B hB
  have hda : (diagonal a).det ≠ 0 := by
    obtain ⟨P, hP, hBP⟩ := hBa
    intro h0
    apply hdet
    rw [hBP, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]
  rw [Matrix.det_diagonal, Fin.prod_univ_three] at hda
  have ha0 : a 0 ≠ 0 := fun h => hda (by simp [h])
  have ha1 : a 1 ≠ 0 := fun h => hda (by simp [h])
  have ha2 : a 2 ≠ 0 := fun h => hda (by simp [h])
  set d := a 0 * a 1 * a 2 with hd
  have hd0 : d ≠ 0 := by rw [hd]; exact mul_ne_zero (mul_ne_zero ha0 ha1) ha2
  have hdiag_eq : diagonal a = diagonal ![a 0, a 1, a 2] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  have h1 : SymCongr B (diagonal ![1, 1, d]) := by
    refine hBa.trans ?_
    rw [hdiag_eq]
    exact symCongr_diag_one_one h2 ha0 ha1 ha2
  set c : k := d / 2 with hc
  have hc0 : c ≠ 0 := div_ne_zero hd0 h2
  have h2c : (-2 : k) * c ≠ 0 := mul_ne_zero (neg_ne_zero.2 h2) hc0
  have h3 : SymCongr (c • sym2Form k) (diagonal ![1, 1, c * (-2 * c) * -c]) :=
    (symCongr_smul_sym2Form h2 c).symm.trans
      (symCongr_diag_one_one h2 hc0 h2c (neg_ne_zero.2 hc0))
  have hsq : c * (-2 * c) * -c = d * (d / 2) ^ 2 := by
    rw [hc]; field_simp
  have h4 : SymCongr (diagonal ![1, 1, d]) (diagonal ![1, 1, c * (-2 * c) * -c]) := by
    rw [hsq]
    exact (symCongr_diag_scale (d := d) (div_ne_zero hd0 h2)).symm
  obtain ⟨P, hP, hBP⟩ := (h1.trans h4).trans h3.symm
  refine ⟨((Matrix.isUnit_iff_isUnit_det P).2 hP).unit, Units.mk0 c hc0, ?_⟩
  rw [hBP, IsUnit.unit_spec, Units.val_mk0, Matrix.mul_smul, Matrix.smul_mul]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
