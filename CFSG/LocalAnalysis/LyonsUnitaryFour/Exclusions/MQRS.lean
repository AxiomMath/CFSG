module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.Tools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.ExclusionArithmetic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι} {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_ne_M (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .M := by
  intro hM
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, hrx₁, hrx₂, hrx₃, -, Ix⟩ :=
    exists_fiber_triple (f := f) (R := (1, 0, 1, 0, 0, 0)) (by rw [hM]; decide)
  obtain ⟨χq, hq, hrq, -, Iq⟩ :=
    exists_fiber_single (f := f) (R := (0, 1, 0, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χw, hw, hrw, -, Iw⟩ :=
    exists_fiber_single (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y₁, hy₁, y₂, hy₂, hry₁, hry₂, hy₁p, hy₂p, -, Ip⟩ :=
    hD.exists_fiber_principal_triple (by rw [hM]; decide)
  rw [principalRow] at Ip
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.isValue, Ix, Iq, Iw, Ip] at r_a r_b
  push_cast at r_a r_b
  apply lyons_M_arithmetic (f x₁) (f x₂) (f x₃) (f χq) (f y₁) (f y₂) (f χw)
    (hD.abs_degree_ge_of_row hx₁ hrx₁ (by decide))
    (hD.abs_degree_ge_of_row hx₂ hrx₂ (by decide))
    (hD.abs_degree_ge_of_row hx₃ hrx₃ (by decide))
    (hD.abs_degree_ge_of_row hq hrq (by decide)) (hD.degree_ge y₁ hy₁ hy₁p)
    (hD.degree_ge y₂ hy₂ hy₂p) (hD.abs_degree_ge_of_row hw hrw (by decide))
    (hD.modEq_of_row hx₁ hrx₁ (by decide)) (hD.modEq_of_row hx₂ hrx₂ (by decide))
    (hD.modEq_of_row hx₃ hrx₃ (by decide)) (hD.modEq_of_row hy₁ hry₁ (by decide))
    (hD.modEq_of_row hy₂ hry₂ (by decide)) (hD.modEq_of_row hq hrq (by decide))
    (hD.modEq_of_row hw hrw (by decide))
  simp only [div_eq_mul_inv]
  linear_combination r_a - r_b

theorem lyons_signedDegree_ne_Q (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .Q := by
  intro hM
  obtain ⟨χx, hx, hrx, -, Ix⟩ :=
    exists_fiber_single (f := f) (R := (1, 0, 0, 0, 0, 1)) (by rw [hM]; decide)
  obtain ⟨h₁, hh₁, h₂, hh₂, h₃, hh₃, hrh₁, hrh₂, hrh₃, -, Ih⟩ :=
    exists_fiber_triple (f := f) (R := (0, 1, 0, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, -, Iz⟩ :=
    exists_fiber_single (f := f) (R := (-3, 1, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χw, hw, hrw, -, Iw⟩ :=
    exists_fiber_single (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨y, hy, hry, hyp, -, Ip⟩ := hD.exists_fiber_principal_pair (by rw [hM]; decide)
  rw [principalRow] at Ip
  obtain ⟨-, -, -, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (1, 0, 0, 0, 0, 1)
  obtain ⟨-, -, -, J₂, J₃, J₄⟩ := hD.fiber_rotate_cycle (0, 1, 0, 1, 1, 1)
  simp only [LyonsRow.rotate] at I₂ I₃ I₄ J₂ J₃ J₄
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, I₂, I₃, I₄, J₂, J₃,
    J₄, Ix, Ih, Iz, Iw, Ip] at r_u r_a r_b
  push_cast at r_u r_a r_b
  apply lyons_Q_arithmetic (f χx) (f h₁) (f h₂) (f h₃) (f χz) (f y) (f χw)
    (hD.abs_degree_ge_of_row hx hrx (by decide)) (hD.degree_ge y hy hyp)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hy hry (by decide))
    (hD.modEq_of_row hh₁ hrh₁ (by decide)) (hD.modEq_of_row hh₂ hrh₂ (by decide))
    (hD.modEq_of_row hh₃ hrh₃ (by decide)) (hD.modEq_of_row hw hrw (by decide))
    (hD.modEq_of_row hz hrz (by decide)) (hD.le_of_pos_of_row hz hrz (by decide))
  · simp only [div_eq_mul_inv]
    linear_combination r_u + r_a - r_b
  · have h : -(4 : ℚ) / f χx + 64 / f h₁ + 64 / f h₂ + 64 / f h₃ + 100 / f χz = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a - r_u
    rw [h]
    exact hD.P_pos

theorem lyons_signedDegree_ne_R (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .R := by
  intro hM
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (1, 0, 0, 0, 0, 1)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, Fz, Iz⟩ :=
    exists_fiber_single (f := f) (R := (-3, 1, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨h₁, hh₁, h₂, hh₂, hrh₁, hrh₂, Fh, Ih⟩ :=
    exists_fiber_pair (f := f) (R := (1, 1, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨Fp, Ip⟩ := hD.fiber_principal_single (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (1, 0, 0, 0, 0, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄
  have e_u := hD.degree_eq_rows hM 0
  have r_u := hD.reciprocal_rows_zero hM
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Fin.isValue, F₂, F₃, F₄, I₂, I₃,
    I₄, Fx, Fz, Fh, Fp, Ix, Iz, Ih, Ip] at e_u r_u
  push_cast at e_u r_u
  apply lyons_R_arithmetic (f χx) (f χz) (f h₁) (f h₂)
    (hD.abs_degree_ge_of_row hx hrx (by decide)) (hD.modEq_of_row hx hrx (by decide))
    (hD.modEq_of_row hz hrz (by decide)) (hD.modEq_of_row hh₁ hrh₁ (by decide))
    (hD.modEq_of_row hh₂ hrh₂ (by decide)) (hD.le_of_pos_of_row hz hrz (by decide))
    (hD.le_of_neg_of_row hh₁ hrh₁ (by decide)) (hD.le_of_neg_of_row hh₂ hrh₂ (by decide))
  · exact_mod_cast
      (by linear_combination e_u : (1 + 4 * f χx - 3 * f χz + f h₁ + f h₂ : ℚ) = 0)
  · simp only [div_eq_mul_inv]
    linear_combination r_u

theorem lyons_signedDegree_ne_S (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .S := by
  intro hM
  obtain ⟨χx, hx, hrx, -, Ix⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 0, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χq, hq, hrq, -, Iq⟩ :=
    exists_fiber_single (f := f) (R := (-2, 0, 0, 1, 0, 1)) (by rw [hM]; decide)
  obtain ⟨h₁, hh₁, h₂, hh₂, hrh₁, hrh₂, -, Ih⟩ :=
    exists_fiber_pair (f := f) (R := (1, 1, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨χw, hw, hrw, -, Iw⟩ :=
    exists_fiber_single (f := f) (R := (0, 0, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨-, Ip⟩ := hD.fiber_principal_single (by rw [hM]; decide)
  rw [principalRow] at Ip
  obtain ⟨-, -, -, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (-1, 1, 0, 0, 1, 1)
  obtain ⟨-, J₂⟩ := hD.fiber_rotate (-2, 0, 0, 1, 0, 1)
  obtain ⟨-, -, -, K₂, K₃, K₄⟩ := hD.fiber_rotate_cycle (0, 1, 0, 1, 1, 1)
  simp only [LyonsRow.rotate] at I₂ I₃ I₄ J₂ K₂ K₃ K₄
  have r_u := hD.reciprocal_rows_zero hM
  have r_a := hD.reciprocal_rows hM 1 (by decide)
  have r_b := hD.reciprocal_rows hM 2 (by decide)
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, I₂, I₃, I₄, J₂, K₂,
    K₃, K₄, Ix, Iq, Ih, Iw, Ip] at r_u r_a r_b
  push_cast at r_u r_a r_b
  apply lyons_S_arithmetic (f χx) (f χq) (f h₁) (f h₂) (f χw)
    (hD.modEq_of_row hx hrx (by decide)) (hD.modEq_of_row hq hrq (by decide))
    (hD.modEq_of_row hh₁ hrh₁ (by decide)) (hD.modEq_of_row hh₂ hrh₂ (by decide))
    (hD.modEq_of_row hw hrw (by decide)) (hD.le_of_pos_of_row hq hrq (by decide))
    (hD.le_of_neg_of_row hh₁ hrh₁ (by decide)) (hD.le_of_neg_of_row hh₂ hrh₂ (by decide))
  have h : (8 : ℚ) - 144 / f χx - 96 / f χq + 100 / f h₁ + 100 / f h₂ - 64 / f χw = -P := by
    simp only [div_eq_mul_inv]
    linear_combination 5 * r_u + 3 * r_a - 4 * r_b
  rw [h]
  linarith [hD.P_pos]

end CFSG.LyonsUnitaryFour
