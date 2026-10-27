module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

universe u

variable {E : Type u} [Field E] (sigma : E ≃+* E)

theorem hyperbolic_isometry_iff_matrix (A : Matrix (Fin 2) (Fin 2) E) :
    (∀ x y, hyperbolicForm sigma (A *ᵥ x) (A *ᵥ y) = hyperbolicForm sigma x y) ↔
      conjTr sigma A * hyperbolicMatrix * A = hyperbolicMatrix := by
  constructor
  · intro h
    ext i j
    have hij := h (Pi.single i 1) (Pi.single j 1)
    change CatalogueBHermitian.matrixForm sigma hyperbolicMatrix
      (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single j 1) =
      CatalogueBHermitian.matrixForm sigma hyperbolicMatrix
        (Pi.single i 1) (Pi.single j 1) at hij
    rw [CatalogueBHermitian.matrixForm_mulVec,
      CatalogueBHermitian.matrixForm_apply, herm_single_left,
      herm_single_left, map_one, one_mul, mulVec_single_one,
      mulVec_single_one] at hij
    simpa only [Matrix.col_apply, one_mul] using hij
  · intro h x y
    change CatalogueBHermitian.matrixForm sigma hyperbolicMatrix (A *ᵥ x) (A *ᵥ y) = _
    rw [CatalogueBHermitian.matrixForm_mulVec, h]
    rfl

theorem hyperbolic_isometry_iff_inverse (M : SpecialLinearGroup (Fin 2) E) :
    (∀ x y, hyperbolicForm sigma (M.val *ᵥ x) (M.val *ᵥ y) =
      hyperbolicForm sigma x y) ↔
    hyperbolicMatrix * conjTr sigma M.val * hyperbolicMatrix =
      (M⁻¹ : SpecialLinearGroup (Fin 2) E).val := by
  rw [hyperbolic_isometry_iff_matrix]
  have hmul : M.val * (M⁻¹ : SpecialLinearGroup (Fin 2) E).val = 1 := by
    change (M * M⁻¹ : SpecialLinearGroup (Fin 2) E).val = 1
    rw [mul_inv_cancel]
    rfl
  have hinv : (M⁻¹ : SpecialLinearGroup (Fin 2) E).val * M.val = 1 := by
    change (M⁻¹ * M : SpecialLinearGroup (Fin 2) E).val = 1
    rw [inv_mul_cancel]
    rfl
  have hH : (hyperbolicMatrix : Matrix (Fin 2) (Fin 2) E) * hyperbolicMatrix = 1 :=
    (hyperbolicGL : GL (Fin 2) E).val_inv
  constructor
  · intro h
    calc
      hyperbolicMatrix * conjTr sigma M.val * hyperbolicMatrix =
          (hyperbolicMatrix * (conjTr sigma M.val * hyperbolicMatrix * M.val)) *
            (M⁻¹ : SpecialLinearGroup (Fin 2) E).val := by
        simp only [Matrix.mul_assoc, hmul, Matrix.mul_one]
      _ = (hyperbolicMatrix * hyperbolicMatrix) *
          (M⁻¹ : SpecialLinearGroup (Fin 2) E).val := by rw [h]
      _ = (M⁻¹ : SpecialLinearGroup (Fin 2) E).val := by rw [hH, Matrix.one_mul]
  · intro h
    calc
      conjTr sigma M.val * hyperbolicMatrix * M.val =
          hyperbolicMatrix * (hyperbolicMatrix * conjTr sigma M.val *
            hyperbolicMatrix) * M.val := by
        simp only [← Matrix.mul_assoc, hH, Matrix.one_mul]
      _ = hyperbolicMatrix * (M⁻¹ : SpecialLinearGroup (Fin 2) E).val * M.val := by
        rw [h]
      _ = hyperbolicMatrix := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem hyperbolic_adjoint_entries (A : Matrix (Fin 2) (Fin 2) E) :
    hyperbolicMatrix * conjTr sigma A * hyperbolicMatrix =
      !![sigma (A 1 1), sigma (A 0 1); sigma (A 1 0), sigma (A 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMatrix, conjTr, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]

theorem hyperbolic_special_iff_entries (M : SpecialLinearGroup (Fin 2) E) :
    (∀ x y, hyperbolicForm sigma (M.val *ᵥ x) (M.val *ᵥ y) =
      hyperbolicForm sigma x y) ↔
    sigma (M.val 0 0) = M.val 0 0 ∧ sigma (M.val 1 1) = M.val 1 1 ∧
      sigma (M.val 0 1) = -M.val 0 1 ∧ sigma (M.val 1 0) = -M.val 1 0 := by
  rw [hyperbolic_isometry_iff_inverse, hyperbolic_adjoint_entries]
  have hinv : (M⁻¹ : SpecialLinearGroup (Fin 2) E).val =
      !![M.val 1 1, -M.val 0 1; -M.val 1 0, M.val 0 0] :=
    Matrix.adjugate_fin_two M.val
  rw [hinv]
  constructor
  · intro h
    exact ⟨congrFun₂ h 1 1, congrFun₂ h 0 0, congrFun₂ h 0 1, congrFun₂ h 1 0⟩
  · rintro ⟨ha, hd, hb, hc⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hd, hb, hc]

@[expose] def diagonalGL (t : Eˣ) : GL (Fin 2) E where
  val := !![(t : E), 0; 0, 1]
  inv := !![((t⁻¹ : Eˣ) : E), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonalGL_val (t : Eˣ) : (diagonalGL t).val = !![(t : E), 0; 0, 1] := rfl

theorem diagonalGL_inv_val (t : Eˣ) :
    (diagonalGL t)⁻¹.val = !![((t⁻¹ : Eˣ) : E), 0; 0, 1] := rfl

@[expose] def conjugatedMatrix (t : Eˣ) (A : Matrix (Fin 2) (Fin 2) E) :
    Matrix (Fin 2) (Fin 2) E :=
  !![A 0 0, A 0 1 / (t : E); A 1 0 * (t : E), A 1 1]

theorem conjugatedMatrix_det (t : Eˣ) (A : Matrix (Fin 2) (Fin 2) E) :
    (conjugatedMatrix t A).det = A.det := by
  rw [conjugatedMatrix, Matrix.det_fin_two_of, Matrix.det_fin_two]
  field_simp

@[expose] def diagonalConjugation (t : Eˣ) :
    SpecialLinearGroup (Fin 2) E ≃* SpecialLinearGroup (Fin 2) E where
  toFun M := ⟨conjugatedMatrix t M.val, (conjugatedMatrix_det t M.val).trans M.property⟩
  invFun M := ⟨conjugatedMatrix t⁻¹ M.val,
    (conjugatedMatrix_det t⁻¹ M.val).trans M.property⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjugatedMatrix, div_eq_mul_inv]
  right_inv M := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjugatedMatrix, div_eq_mul_inv]
  map_mul' M N := by
    apply Subtype.ext
    change conjugatedMatrix t (M.val * N.val) =
      conjugatedMatrix t M.val * conjugatedMatrix t N.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjugatedMatrix, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
      <;> field_simp

theorem diagonalConjugation_val (t : Eˣ) (M : SpecialLinearGroup (Fin 2) E) :
    (diagonalConjugation t M).val = (diagonalGL t)⁻¹.val * M.val * (diagonalGL t).val := by
  change conjugatedMatrix t M.val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugatedMatrix, diagonalGL,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      div_eq_mul_inv, mul_comm]

theorem diagonalConjugation_entries (t : Eˣ) (M : SpecialLinearGroup (Fin 2) E) :
    (diagonalConjugation t M).val =
      !![M.val 0 0, M.val 0 1 / (t : E); M.val 1 0 * (t : E), M.val 1 1] := rfl

theorem antifixed_iff_mul_fixed (t : Eˣ) (ht : sigma (t : E) = -(t : E)) (x : E) :
    sigma x = -x ↔ sigma (x * (t : E)) = x * (t : E) := by
  rw [map_mul, ht]
  constructor
  · intro hx
    rw [hx, neg_mul_neg]
  · intro hx
    have heq : (sigma x + x) * (t : E) = 0 := by linear_combination -hx
    exact (add_eq_zero_iff_eq_neg).mp ((mul_eq_zero.mp heq).resolve_right t.ne_zero)

theorem hyperbolic_iff_conjugation_fixed (t : Eˣ) (ht : sigma (t : E) = -(t : E))
    (M : SpecialLinearGroup (Fin 2) E) :
    (∀ x y, hyperbolicForm sigma (M.val *ᵥ x) (M.val *ᵥ y) =
      hyperbolicForm sigma x y) ↔
    ∀ i j, sigma ((diagonalConjugation t M).val i j) =
      (diagonalConjugation t M).val i j := by
  rw [hyperbolic_special_iff_entries]
  simp only [diagonalConjugation_entries]
  constructor
  · rintro ⟨ha, hd, hb, hc⟩ i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact (antifixed_iff_div_fixed sigma t ht _).mp hb
    · exact (antifixed_iff_mul_fixed sigma t ht _).mp hc
    · exact hd
  · intro h
    exact ⟨h 0 0, h 1 1, (antifixed_iff_div_fixed sigma t ht _).mpr (h 0 1),
      (antifixed_iff_mul_fixed sigma t ht _).mpr (h 1 0)⟩

end CFSG.ComponentClassification.CatalogueBUnitaryTwo
