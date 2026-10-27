module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.Tools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.ExclusionArithmetic

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι} {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_ne_C1 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .C1 := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, -1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨w₁, hw₁, w₂, hw₂, hrw₁, hrw₂, Fw, Iw⟩ :=
    exists_fiber_pair (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y, hy, hry, hyp, Fp, Ip⟩ := hD.exists_fiber_principal_pair (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, -1, 1, 1, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fw, Fp, Iq, Ix, Iw, Ip] at e_u e_a r_u r_a r_b
  push_cast at e_u e_a r_u r_a r_b
  apply lyons_CEF_arithmetic (f χx) (f χq) (f y) (f w₁) (f w₂) (hD.degree_ge y hy hyp)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy hry (by decide))
    (hD.modEq_of_row hw₁ hrw₁ (by decide)) (hD.modEq_of_row hw₂ hrw₂ (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

theorem lyons_signedDegree_ne_C2 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .C2 := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 0, 2)) (by rw [hM]; decide)
  obtain ⟨w₁, hw₁, w₂, hw₂, hrw₁, hrw₂, Fw, Iw⟩ :=
    exists_fiber_pair (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y, hy, hry, hyp, Fp, Ip⟩ := hD.exists_fiber_principal_pair (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 0, 2)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fw, Fp, Iq, Ix, Iw, Ip] at e_u e_a r_u r_a r_b
  push_cast at e_u e_a r_u r_a r_b
  apply lyons_CEF_arithmetic (f χx) (f χq) (f y) (f w₁) (f w₂) (hD.degree_ge y hy hyp)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy hry (by decide))
    (hD.modEq_of_row hw₁ hrw₁ (by decide)) (hD.modEq_of_row hw₂ hrw₂ (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

theorem lyons_signedDegree_ne_E1 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .E1 := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, -1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨w₁, hw₁, w₂, hw₂, hrw₁, hrw₂, Fw, Iw⟩ :=
    exists_fiber_pair (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y, hy, hry, hyp, Fp, Ip⟩ := hD.exists_fiber_principal_pair (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, -1, 1, 1, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fw, Fp, Iq, Ix, Iw, Ip] at e_u e_a r_u r_a r_b
  push_cast at e_u e_a r_u r_a r_b
  apply lyons_CEF_arithmetic (f χx) (f χq) (f y) (f w₁) (f w₂) (hD.degree_ge y hy hyp)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy hry (by decide))
    (hD.modEq_of_row hw₁ hrw₁ (by decide)) (hD.modEq_of_row hw₂ hrw₂ (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

theorem lyons_signedDegree_ne_E2 (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .E2 := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 0, 2)) (by rw [hM]; decide)
  obtain ⟨w₁, hw₁, w₂, hw₂, hrw₁, hrw₂, Fw, Iw⟩ :=
    exists_fiber_pair (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y, hy, hry, hyp, Fp, Ip⟩ := hD.exists_fiber_principal_pair (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 0, 2)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fw, Fp, Iq, Ix, Iw, Ip] at e_u e_a r_u r_a r_b
  push_cast at e_u e_a r_u r_a r_b
  apply lyons_CEF_arithmetic (f χx) (f χq) (f y) (f w₁) (f w₂) (hD.degree_ge y hy hyp)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy hry (by decide))
    (hD.modEq_of_row hw₁ hrw₁ (by decide)) (hD.modEq_of_row hw₂ hrw₂ (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

theorem lyons_signedDegree_ne_F (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .F := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 1, 1)) (by rw [hM]; decide)
  obtain ⟨w₁, hw₁, w₂, hw₂, hrw₁, hrw₂, Fw, Iw⟩ :=
    exists_fiber_pair (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y, hy, hry, hyp, Fp, Ip⟩ := hD.exists_fiber_principal_pair (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 1, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  obtain ⟨G₂, G₃, G₄, J₂, J₃, J₄⟩ := hD.fiber_rotate_cycle (1, 1, 0, 1, 1, 2)
  simp only [LyonsRow.rotate] at G₂ G₃ G₄ J₂ J₃ J₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    G₂, G₃, G₄, J₂, J₃, J₄,
    F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fw, Fp, Iq, Ix, Iw, Ip] at e_u e_a r_u r_a r_b
  push_cast at e_u e_a r_u r_a r_b
  apply lyons_CEF_arithmetic (f χx) (f χq) (f y) (f w₁) (f w₂) (hD.degree_ge y hy hyp)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy hry (by decide))
    (hD.modEq_of_row hw₁ hrw₁ (by decide)) (hD.modEq_of_row hw₂ hrw₂ (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

theorem lyons_signedDegree_ne_FReflected (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .FReflected := by
  intro hM
  obtain ⟨χq, hq, hrq, Fq, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 2, 2, 2, 2, 2)) (by rw [hM]; decide)
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 1, 1)) (by rw [hM]; decide)
  obtain ⟨w₁, hw₁, w₂, hw₂, hrw₁, hrw₂, Fw, Iw⟩ :=
    exists_fiber_pair (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y, hy, hry, hyp, Fp, Ip⟩ := hD.exists_fiber_principal_pair (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 1, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  obtain ⟨G₂, G₃, G₄, J₂, J₃, J₄⟩ := hD.fiber_rotate_cycle (1, 1, 0, 2, 1, 1)
  simp only [LyonsRow.rotate] at G₂ G₃ G₄ J₂ J₃ J₄
  have e_u := hD.degree_eq_rows hM 0
  have e_a := hD.degree_eq_rows hM 1
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    G₂, G₃, G₄, J₂, J₃, J₄,
    F₂, F₃, F₄, I₂, I₃, I₄, Fq, Fx, Fw, Fp, Iq, Ix, Iw, Ip] at e_u e_a r_u r_a r_b
  push_cast at e_u e_a r_u r_a r_b
  apply lyons_CEF_arithmetic (f χx) (f χq) (f y) (f w₁) (f w₂) (hD.degree_ge y hy hyp)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy hry (by decide))
    (hD.modEq_of_row hw₁ hrw₁ (by decide)) (hD.modEq_of_row hw₂ hrw₂ (by decide))
    (hD.le_of_pos_of_row hq hrq (by decide))
  · exact_mod_cast (by linear_combination e_a - e_u : (8 * f χx + 4 * f χq : ℚ) = 0)
  · have h : (72 : ℚ) / f χx + 400 / f χq = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos
  · simp only [div_eq_mul_inv]
    linear_combination r_a - r_b

end CFSG.LyonsUnitaryFour
