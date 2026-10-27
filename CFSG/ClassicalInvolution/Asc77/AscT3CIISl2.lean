module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem tr_eq_zero_of_sq_eq_neg_one (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 2) (Fin 2) F}
    (hX2 : X * X = -1) (hdet : X.det = 1) : X 0 0 + X 1 1 = 0 := by
  have h00 := congrFun (congrFun hX2 0) 0
  have h01 := congrFun (congrFun hX2 0) 1
  have h10 := congrFun (congrFun hX2 1) 0
  have h11 := congrFun (congrFun hX2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  by_contra hne
  have e1 : X 0 1 = 0 := by
    have : X 0 1 * (X 0 0 + X 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hne
  have e2 : X 1 0 = 0 := by
    have : X 1 0 * (X 0 0 + X 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hne
  have e3 : X 0 0 - X 1 1 = 0 := by
    have : (X 0 0 - X 1 1) * (X 0 0 + X 1 1) = 0 := by
      linear_combination h00 - h11
    exact (mul_eq_zero.mp this).resolve_right hne
  have e4 : X 0 0 = X 1 1 := by linear_combination e3
  rw [e1, e2, ← e4] at hdet
  rw [e1, e2] at h00
  apply h2
  linear_combination h00 - hdet

def sl2ColMat (X : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  !![v 0, X 0 0 * v 0 + X 0 1 * v 1; v 1, X 1 0 * v 0 + X 1 1 * v 1]

theorem mul_sl2ColMat {X : Matrix (Fin 2) (Fin 2) F} (hX2 : X * X = -1) (v : Fin 2 → F) :
    X * sl2ColMat X v = sl2ColMat X v * !![0, -1; 1, 0] := by
  have h00 := congrFun (congrFun hX2 0) 0
  have h01 := congrFun (congrFun hX2 0) 1
  have h10 := congrFun (congrFun hX2 1) 0
  have h11 := congrFun (congrFun hX2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2ColMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination v 0 * h00 + v 1 * h01
  · linear_combination v 0 * h10 + v 1 * h11

theorem exists_sl2ColMat (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 2) (Fin 2) F} (hX2 : X * X = -1)
    (hdet : X.det = 1) : ∃ v : Fin 2 → F, (sl2ColMat X v).det ≠ 0 := by
  have htr := tr_eq_zero_of_sq_eq_neg_one h2 hX2 hdet
  by_contra hcon
  push Not at hcon
  have d1 := hcon ![1, 0]
  have d2 := hcon ![0, 1]
  have d3 := hcon ![1, 1]
  simp [sl2ColMat, Matrix.det_fin_two] at d1 d2 d3
  rw [Matrix.det_fin_two] at hdet
  have e1 : X 1 0 = 0 := d1
  have e2 : X 0 1 = 0 := d2
  have e3 : X 1 1 = X 0 0 := by linear_combination d3 - d1 + d2
  rw [e1, e2, e3] at hdet
  have e4 : X 0 0 = 0 := by
    have : 2 * X 0 0 = 0 := by linear_combination htr - e3
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [e4] at hdet
  simp at hdet

theorem exists_sl2_conj_of_sq_eq_neg_one [Finite F] (hodd : Odd (Nat.card F))
    {x y : SL(2, F)} (hx : x * x = -1) (hy : y * y = -1) : ∃ g : SL(2, F), g * x = y * g := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hXdef
  set Y : Matrix (Fin 2) (Fin 2) F := (y : Matrix (Fin 2) (Fin 2) F) with hYdef
  have hX2 : X * X = -1 := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hx
    simpa using this
  have hY2 : Y * Y = -1 := by
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hy
    simpa using this
  have hXdet : X.det = 1 := x.2
  have hYdet : Y.det = 1 := y.2
  obtain ⟨v, hv⟩ := exists_sl2ColMat h2 hX2 hXdet
  obtain ⟨w, hw⟩ := exists_sl2ColMat h2 hY2 hYdet
  set P := sl2ColMat X v with hP
  set Q := sl2ColMat Y w with hQ
  set C : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0] with hC
  have hXP : X * P = P * C := mul_sl2ColMat hX2 v
  have hYQ : Y * Q = Q * C := mul_sl2ColMat hY2 w
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hv)
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  obtain ⟨a, b, hab⟩ := CFSG.Semidihedral.OddFieldSL2.sum_two_squares F hodd (P.det / Q.det)
  set Z : Matrix (Fin 2) (Fin 2) F := a • (1 : Matrix (Fin 2) (Fin 2) F) + b • X with hZ
  have htr := tr_eq_zero_of_sq_eq_neg_one h2 hX2 hXdet
  have hZdet : Z.det = a ^ 2 + b ^ 2 := by
    rw [hZ, Matrix.det_fin_two]
    rw [Matrix.det_fin_two] at hXdet
    simp
    linear_combination (a * b) * htr + b ^ 2 * hXdet
  have hZX : Z * X = X * Z := by
    rw [hZ]
    simp [add_mul, mul_add]
  set M : Matrix (Fin 2) (Fin 2) F := Q * P⁻¹ * Z with hM
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hdetPinv : P⁻¹.det = (P.det)⁻¹ := by
    have := congrArg Matrix.det hPinv
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact eq_inv_of_mul_eq_one_right this
  have hMdet : M.det = 1 := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, hdetPinv, hZdet, hab]
    have h1 : P.det ≠ 0 := hv
    have h2' : Q.det ≠ 0 := hw
    field_simp
  have hPX : P⁻¹ * X = C * P⁻¹ := by
    calc P⁻¹ * X = P⁻¹ * X * (P * P⁻¹) := by rw [hPinv, mul_one]
      _ = P⁻¹ * (X * P) * P⁻¹ := by simp only [mul_assoc]
      _ = P⁻¹ * (P * C) * P⁻¹ := by rw [hXP]
      _ = C * P⁻¹ := by rw [← mul_assoc, hPinv', one_mul]
  have hMX : M * X = Y * M := by
    calc M * X = Q * P⁻¹ * (Z * X) := by rw [hM, mul_assoc]
      _ = Q * P⁻¹ * (X * Z) := by rw [hZX]
      _ = (Q * (P⁻¹ * X)) * Z := by simp only [mul_assoc]
      _ = (Q * (C * P⁻¹)) * Z := by rw [hPX]
      _ = ((Q * C) * P⁻¹) * Z := by simp only [mul_assoc]
      _ = ((Y * Q) * P⁻¹) * Z := by rw [← hYQ]
      _ = Y * M := by rw [hM]; simp only [mul_assoc]
  refine ⟨⟨M, hMdet⟩, Subtype.ext ?_⟩
  exact hMX


theorem exists_conj_of_sq_eq_of_equiv_sl2 {F : Type*} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {P : Type*} [Group P] (e : P ≃* SL(2, F)) {z : P}
    (hz : e z = -1) {k h : P} (hk : k * k = z) (hh : h * h = z) :
    ∃ x : P, x * k * x⁻¹ = h := by
  have hk' : e k * e k = -1 := by rw [← map_mul, hk, hz]
  have hh' : e h * e h = -1 := by rw [← map_mul, hh, hz]
  obtain ⟨g, hg⟩ := exists_sl2_conj_of_sq_eq_neg_one hodd hk' hh'
  refine ⟨e.symm g, ?_⟩
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
  group

end CFSG.ClassicalInvolution.Asc77.T3CII
