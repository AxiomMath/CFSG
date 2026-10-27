module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.Tools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.ExclusionArithmetic

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι} {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_ne_H (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .H := by
  intro hM
  obtain ⟨χx, hx, hrx, Fx, Ix⟩ :=
    exists_fiber_single (f := f) (R := (1, 1, 0, 1, 2, 1)) (by rw [hM]; decide)
  obtain ⟨χy, hy, hry, Fy, Iy⟩ :=
    exists_fiber_single (f := f) (R := (-1, 1, 0, 1, 0, 1)) (by rw [hM]; decide)
  obtain ⟨χz, hz, hrz, Fz, Iz⟩ :=
    exists_fiber_single (f := f) (R := (-3, 1, 1, 1, 1, 1)) (by rw [hM]; decide)
  obtain ⟨Fp, Ip⟩ := hD.fiber_principal_single (by rw [hM]; decide)
  rw [principalRow] at Fp Ip
  obtain ⟨F₂, F₃, F₄, I₂, I₃, I₄⟩ := hD.fiber_rotate_cycle (1, 1, 0, 1, 2, 1)
  obtain ⟨G₂, J₂⟩ := hD.fiber_rotate (-1, 1, 0, 1, 0, 1)
  simp only [LyonsRow.rotate] at F₂ F₃ F₄ I₂ I₃ I₄ G₂ J₂
  have e_u := hD.degree_eq_rows hM 0
  have r_u := hD.reciprocal_rows_zero hM
  simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Fin.isValue, F₂, F₃, F₄, I₂, I₃,
    I₄, G₂, J₂, Fx, Fy, Fz, Fp, Ix, Iy, Iz, Ip] at e_u r_u
  push_cast at e_u r_u
  apply lyons_H_arithmetic (f χx) (f χy) (f χz) (hD.modEq_of_row hx hrx (by decide))
    (hD.modEq_of_row hy hry (by decide)) (hD.modEq_of_row hz hrz (by decide))
    (hD.le_of_neg_of_row hx hrx (by decide)) (hD.le_of_pos_of_row hz hrz (by decide))
  · exact_mod_cast
      (by linear_combination e_u : (1 + 4 * f χx - 2 * f χy - 3 * f χz : ℚ) = 0)
  · simp only [div_eq_mul_inv]
    linear_combination r_u

end CFSG.LyonsUnitaryFour
