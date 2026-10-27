module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

def colPair (X : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  !![v 0, (X *ᵥ v) 0; v 1, (X *ᵥ v) 1]

def compMat : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]

theorem mul_colPair (X : Matrix (Fin 2) (Fin 2) F) (hX : X * X = -1) (v : Fin 2 → F) :
    X * colPair X v = colPair X v * compMat := by
  have h2 : X *ᵥ (X *ᵥ v) = -v := by
    rw [Matrix.mulVec_mulVec, hX, Matrix.neg_mulVec, Matrix.one_mulVec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colPair, compMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] at h2 ⊢
  all_goals first | simpa using congrFun h2 0 | simpa using congrFun h2 1

theorem exists_det_colPair_ne_zero (X : Matrix (Fin 2) (Fin 2) F) (hX : X * X = -1)
    (hdet : X.det = 1) (h2 : (2 : F) ≠ 0) : ∃ v : Fin 2 → F, (colPair X v).det ≠ 0 := by
  have e00 := congrFun (congrFun hX 0) 0
  have e11 := congrFun (congrFun hX 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq] at e00 e11
  rw [Matrix.det_fin_two] at hdet
  by_cases hc : X 1 0 = 0
  · by_cases hb : X 0 1 = 0
    · refine ⟨![1, 1], ?_⟩
      simp only [colPair, Matrix.det_fin_two_of, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simp [hc, hb] at e00 e11 hdet ⊢
      intro h
      have had : X 0 0 = X 1 1 := by linear_combination -h
      apply h2
      have : (2 : F) = 0 := by
        have h3 : X 0 0 * X 1 1 = 1 := by linear_combination hdet
        rw [← had] at h3
        have h4 : X 0 0 * X 0 0 = -1 := by linear_combination e00
        linear_combination h4 - h3
      exact this
    · refine ⟨![0, 1], ?_⟩
      simp only [colPair, Matrix.det_fin_two_of, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      simpa using hb
  · refine ⟨![1, 0], ?_⟩
    simp only [colPair, Matrix.det_fin_two_of, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simpa using hc

theorem trace_eq_zero_of_sq (X : Matrix (Fin 2) (Fin 2) F) (hX : X * X = -1)
    (hdet : X.det = 1) : X 0 0 + X 1 1 = 0 := by
  have e00 := congrFun (congrFun hX 0) 0
  have e01 := congrFun (congrFun hX 0) 1
  have e10 := congrFun (congrFun hX 1) 0
  have e11 := congrFun (congrFun hX 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_cases hb : X 0 1 = 0
  · by_cases hc : X 1 0 = 0
    · rw [hb] at e00 hdet
      rw [hc] at e00 hdet
      have h1 : (X 0 0 + X 1 1) * (X 0 0 + X 1 1) = 0 := by
        rw [hc, hb] at e11
        linear_combination e00 + e11 + 2 * hdet
      exact mul_self_eq_zero.mp h1
    · have : X 1 0 * (X 0 0 + X 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_left hc
  · have : X 0 1 * (X 0 0 + X 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_left hb

theorem sl2_exists_conj_of_sq_eq_neg_one [Finite F] (hodd : Odd (Nat.card F))
    {x y : SL(2, F)} (hx : x * x = -1) (hy : y * y = -1) :
    ∃ g : SL(2, F), g * x * g⁻¹ = y := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hXdef
  set Y : Matrix (Fin 2) (Fin 2) F := (y : Matrix (Fin 2) (Fin 2) F) with hYdef
  have hX : X * X = -1 := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hx
    simpa using this
  have hY : Y * Y = -1 := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hy
    simpa using this
  have hXdet : X.det = 1 := x.2
  have hYdet : Y.det = 1 := y.2
  obtain ⟨v, hv⟩ := exists_det_colPair_ne_zero X hX hXdet h2
  obtain ⟨w, hw⟩ := exists_det_colPair_ne_zero Y hY hYdet h2
  set Px := colPair X v with hPxdef
  set Py := colPair Y w with hPydef
  have hPx := mul_colPair X hX v
  have hPy := mul_colPair Y hY w
  obtain ⟨a, b, hab⟩ :=
    CFSG.Semidihedral.OddFieldSL2.sum_two_squares F hodd (Px.det / Py.det)
  set c : Matrix (Fin 2) (Fin 2) F := a • (1 : Matrix (Fin 2) (Fin 2) F) + b • X with hc
  have hcX : c * X = X * c := by
    simp [hc, add_mul, mul_add]
  have hcdet : c.det = a ^ 2 + b ^ 2 := by
    have htr := trace_eq_zero_of_sq X hX hXdet
    rw [Matrix.det_fin_two] at hXdet ⊢
    simp only [hc, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul]
    linear_combination b ^ 2 * hXdet + a * b * htr
  have hux : IsUnit Px.det := isUnit_iff_ne_zero.mpr hv
  have hPxinv : Px⁻¹ * X = compMat * Px⁻¹ := by
    calc Px⁻¹ * X = Px⁻¹ * X * (Px * Px⁻¹) := by rw [Matrix.mul_nonsing_inv _ hux, mul_one]
      _ = Px⁻¹ * (X * Px) * Px⁻¹ := by simp only [mul_assoc]
      _ = Px⁻¹ * (Px * compMat) * Px⁻¹ := by rw [hPx]
      _ = compMat * Px⁻¹ := by rw [← mul_assoc Px⁻¹ Px, Matrix.nonsing_inv_mul _ hux, one_mul]
  set g : Matrix (Fin 2) (Fin 2) F := Py * Px⁻¹ * c with hg
  have hgdet : g.det = 1 := by
    rw [hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
      hcdet, hab]
    field_simp
  have hgX : g * X = Y * g := by
    calc g * X = Py * Px⁻¹ * (c * X) := by rw [hg, mul_assoc]
      _ = Py * (Px⁻¹ * X) * c := by rw [hcX]; simp only [mul_assoc]
      _ = Py * (compMat * Px⁻¹) * c := by rw [hPxinv]
      _ = (Py * compMat) * Px⁻¹ * c := by simp only [mul_assoc]
      _ = (Y * Py) * Px⁻¹ * c := by rw [hPy]
      _ = Y * g := by rw [hg]; simp only [mul_assoc]
  let gS : SL(2, F) := ⟨g, hgdet⟩
  refine ⟨gS, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact hgX

end CFSG.ClassicalInvolution.Asc77.AscFusion
