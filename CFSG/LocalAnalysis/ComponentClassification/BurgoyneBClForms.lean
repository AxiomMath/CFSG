module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClBasic

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem gram_apply {m : Type*} [Fintype m] (E : Matrix (Fin n) m K) (R : Matrix (Fin n) (Fin n) K)
    (a b : m) : (Eᵀ * R * E) a b = (fun i => E i a) ⬝ᵥ (R *ᵥ fun i => E i b) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, dotProduct, mulVec]

abbrev J₂ (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem J₂_mul_J₂ : J₂ K * J₂ K = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem J₂_transpose : (J₂ K)ᵀ = -J₂ K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem transpose_J₂_mul (g : SL(2, K)) :
    (g : Matrix (Fin 2) (Fin 2) K)ᵀ * J₂ K * (g : Matrix (Fin 2) (Fin 2) K) = J₂ K := by
  have hd := g.2
  rw [det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hd | linear_combination -hd

theorem dotProduct_mulVec_self_of_alt (h2 : (2 : K) ≠ 0) {R : Matrix (Fin n) (Fin n) K}
    (hR : Rᵀ = -R) (v : Fin n → K) : v ⬝ᵥ (R *ᵥ v) = 0 := by
  have h : v ⬝ᵥ (R *ᵥ v) = -(v ⬝ᵥ (R *ᵥ v)) := by
    calc v ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (Rᵀ *ᵥ v) := by
          rw [mulVec_transpose, dotProduct_comm v (v ᵥ* R), ← dotProduct_mulVec]
      _ = -(v ⬝ᵥ (R *ᵥ v)) := by rw [hR, neg_mulVec, dotProduct_neg]
  have h' : (2 : K) * (v ⬝ᵥ (R *ᵥ v)) = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left h2

theorem alt_emb (h2 : (2 : K) ≠ 0) {R : Matrix (Fin n) (Fin n) K} (hR : Rᵀ = -R)
    {e f : Fin n → K} (hef : e ⬝ᵥ (R *ᵥ f) = 1) :
    ∃ (E : Matrix (Fin n) (Fin 2) K) (F : Matrix (Fin 2) (Fin n) K),
      F * E = 1 ∧ Eᵀ * R = J₂ K * F ∧ R * E = Fᵀ * J₂ K := by
  have hfe : f ⬝ᵥ (R *ᵥ e) = -1 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hR, dotProduct_comm, neg_mulVec, dotProduct_neg,
      hef]
  set E : Matrix (Fin n) (Fin 2) K := Matrix.of fun i a => ![e, f] a i with hE
  have hG : Eᵀ * R * E = J₂ K := by
    ext a b
    rw [gram_apply]
    fin_cases a <;> fin_cases b
    · exact dotProduct_mulVec_self_of_alt h2 hR e
    · exact hef
    · exact hfe
    · exact dotProduct_mulVec_self_of_alt h2 hR f
  refine ⟨E, -J₂ K * Eᵀ * R, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, hG, Matrix.neg_mul,
      J₂_mul_J₂, neg_neg]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_neg, J₂_mul_J₂, neg_neg,
      Matrix.one_mul]
  · have hT : (-J₂ K * Eᵀ * R)ᵀ = -(R * E * J₂ K) := by
      rw [transpose_mul, transpose_mul, hR, transpose_transpose, transpose_neg, J₂_transpose,
        neg_neg, Matrix.neg_mul, ← Matrix.mul_assoc]
    rw [hT, Matrix.neg_mul, Matrix.mul_assoc, J₂_mul_J₂, Matrix.mul_neg, Matrix.mul_one,
      neg_neg]

abbrev coord4 (h4 : 4 ≤ n) : Matrix (Fin n) (Fin 4) K :=
  (1 : Matrix (Fin n) (Fin n) K).submatrix id (Fin.castLE h4)

theorem coord4_transpose_mul (h4 : 4 ≤ n) :
    (coord4 (K := K) h4)ᵀ * coord4 (K := K) h4 = 1 := by
  rw [coord4, transpose_submatrix, transpose_one, ← submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.one_mul]
  exact submatrix_one _ (Fin.castLE_injective h4)

theorem coord4_transpose_mul_diag (h4 : 4 ≤ n) {w : Fin n → K}
    (hw : ∀ a : Fin 4, w (Fin.castLE h4 a) = 1) :
    (coord4 (K := K) h4)ᵀ * diagonal w =
      (1 : Matrix (Fin 4) (Fin 4) K) * (coord4 (K := K) h4)ᵀ := by
  rw [Matrix.one_mul]
  ext a j
  rw [mul_diagonal, coord4, transpose_submatrix, transpose_one, submatrix_apply, id,
    one_apply]
  split_ifs with h
  · rw [← h, hw, mul_one]
  · rw [zero_mul]

theorem diag_mul_coord4 (h4 : 4 ≤ n) {w : Fin n → K} (hw : ∀ a : Fin 4, w (Fin.castLE h4 a) = 1) :
    diagonal w * coord4 (K := K) h4 = (coord4 (K := K) h4)ᵀᵀ * (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [transpose_transpose, Matrix.mul_one]
  ext j a
  rw [diagonal_mul, coord4, submatrix_apply, id, one_apply]
  split_ifs with h
  · rw [h, hw, one_mul]
  · rw [mul_zero]

theorem frame_emb (h4 : 4 ≤ n) {R P₀ P₀i : Matrix (Fin n) (Fin n) K} (hP : P₀ * P₀i = 1)
    (hP' : P₀i * P₀ = 1) {w : Fin n → K} (hw : ∀ a : Fin 4, w (Fin.castLE h4 a) = 1)
    (hPR : P₀ᵀ * R * P₀ = diagonal w) :
    ∃ (E : Matrix (Fin n) (Fin 4) K) (F : Matrix (Fin 4) (Fin n) K), F * E = 1 ∧
      Eᵀ * R = (1 : Matrix (Fin 4) (Fin 4) K) * F ∧
      R * E = Fᵀ * (1 : Matrix (Fin 4) (Fin 4) K) := by
  have hT : P₀iᵀ * P₀ᵀ = 1 := by rw [← transpose_mul, hP, transpose_one]
  have hRP : R * P₀ = P₀iᵀ * diagonal w := by
    rw [← hPR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hPR' : P₀ᵀ * R = diagonal w * P₀i := by
    rw [← hPR, Matrix.mul_assoc, hP, Matrix.mul_one]
  refine ⟨P₀ * coord4 (K := K) h4, (coord4 (K := K) h4)ᵀ * P₀i, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P₀i, hP', Matrix.one_mul, coord4_transpose_mul]
  · rw [transpose_mul, Matrix.mul_assoc, hPR', ← Matrix.mul_assoc,
      coord4_transpose_mul_diag h4 hw, Matrix.one_mul, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, hRP, Matrix.mul_assoc, diag_mul_coord4 h4 hw, transpose_mul,
      transpose_transpose, Matrix.mul_one, Matrix.mul_one]

abbrev quatI : Matrix (Fin 4) (Fin 4) K := !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

abbrev quatJ : Matrix (Fin 4) (Fin 4) K := !![0, 0, -1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, -1, 0, 0]

theorem quatI_sq : (quatI : Matrix (Fin 4) (Fin 4) K) * quatI = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem quatJ_sq : (quatJ : Matrix (Fin 4) (Fin 4) K) * quatJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem quatJ_mul_quatI : (quatJ : Matrix (Fin 4) (Fin 4) K) * quatI = -(quatI * quatJ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem quatI_orth : (quatI : Matrix (Fin 4) (Fin 4) K)ᵀ * 1 * quatI = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem quatJ_orth : (quatJ : Matrix (Fin 4) (Fin 4) K)ᵀ * 1 * quatJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

end CFSG.ComponentClassification.Burgoyne.Cl
