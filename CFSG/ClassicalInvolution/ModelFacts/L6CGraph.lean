module

public import CFSG.ClassicalInvolution.ModelFacts.L6CMat
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix Module CFSG.ClassicalInvolution.WeakCT
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_symplectic_basis)
open scoped MatrixGroups

variable {F : Type} [Field F]

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) F

theorem slConj_transpose_inv_fixed {n : ℕ} (A : GL (Fin n) F) (g : SL(n, F))
    (hg : (g : Matrix (Fin n) (Fin n) F)ᵀ * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F) = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    slConjugation n F A (g⁻¹).transpose = g := by
  apply Subtype.ext
  rw [slConjugation_matrix]
  set M := (g : Matrix (Fin n) (Fin n) F) with hM
  set R := ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hR
  change (A : Matrix (Fin n) (Fin n) F) * (adjugate M)ᵀ * R = M
  have hN : (adjugate M)ᵀ * Mᵀ = 1 := by
    rw [← transpose_mul, mul_adjugate, show M.det = 1 from g.2, one_smul, transpose_one]
  have hRM : R * M = (adjugate M)ᵀ * R := by
    calc R * M = ((adjugate M)ᵀ * Mᵀ) * (R * M) := by rw [hN, Matrix.one_mul]
      _ = (adjugate M)ᵀ * (Mᵀ * R * M) := by simp only [Matrix.mul_assoc]
      _ = (adjugate M)ᵀ * R := by rw [hg]
  have hAR : (A : Matrix (Fin n) (Fin n) F) * R = 1 := by
    rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (A : Matrix (Fin n) (Fin n) F) * (adjugate M)ᵀ * R =
        (A : Matrix (Fin n) (Fin n) F) * (R * M) := by rw [Matrix.mul_assoc, hRM]
    _ = M := by rw [← Matrix.mul_assoc, hAR, Matrix.one_mul]

theorem graph_fixed_of_gram (P : GL (Fin 4) F) (R G : 𝕄₄) (hG : (P : 𝕄₄)ᵀ * R * (P : 𝕄₄) = G)
    (hRot : (rot4 F : 𝕄₄)ᵀ * G * (rot4 F : 𝕄₄) = G) :
    ((slConjugation 4 F P (rot4 F) : SL(4, F)) : 𝕄₄)ᵀ * R *
      ((slConjugation 4 F P (rot4 F) : SL(4, F)) : 𝕄₄) = R := by
  have hPQ : (P : 𝕄₄) * ((P⁻¹ : GL (Fin 4) F) : 𝕄₄) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQP : ((P⁻¹ : GL (Fin 4) F) : 𝕄₄) * (P : 𝕄₄) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRR : R = ((P⁻¹ : GL (Fin 4) F) : 𝕄₄)ᵀ * G * ((P⁻¹ : GL (Fin 4) F) : 𝕄₄) := by
    rw [← hG]
    calc R = ((P⁻¹ : GL (Fin 4) F) : 𝕄₄)ᵀ * (P : 𝕄₄)ᵀ * R *
          ((P : 𝕄₄) * ((P⁻¹ : GL (Fin 4) F) : 𝕄₄)) := by
          rw [← Matrix.transpose_mul, hPQ, transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [slConjugation_matrix]
  calc ((P : 𝕄₄) * (rot4 F : 𝕄₄) * ((P⁻¹ : GL (Fin 4) F) : 𝕄₄))ᵀ * R *
        ((P : 𝕄₄) * (rot4 F : 𝕄₄) * ((P⁻¹ : GL (Fin 4) F) : 𝕄₄))
      = ((P⁻¹ : GL (Fin 4) F) : 𝕄₄)ᵀ * ((rot4 F : 𝕄₄)ᵀ * ((P : 𝕄₄)ᵀ * R * (P : 𝕄₄)) *
          (rot4 F : 𝕄₄)) * ((P⁻¹ : GL (Fin 4) F) : 𝕄₄) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((P⁻¹ : GL (Fin 4) F) : 𝕄₄)ᵀ * ((rot4 F : 𝕄₄)ᵀ * G * (rot4 F : 𝕄₄)) *
          ((P⁻¹ : GL (Fin 4) F) : 𝕄₄) := by rw [hG]
    _ = R := by rw [hRot, hRR]

theorem exists_congr_diag_aa4 [Finite F] (h2 : (2 : F) ≠ 0) {R : 𝕄₄} (hR : Rᵀ = R)
    (hRdet : R.det ≠ 0) :
    ∃ (P : GL (Fin 4) F) (a c d : F), a ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
      (P : 𝕄₄)ᵀ * R * (P : 𝕄₄) = Matrix.diagonal ![a, a, c, d] := by
  obtain ⟨g, d, hg⟩ := CFSG.RankThree.PartOne.LIT.exists_diagonal_congr h2 R hR
  have hg0 : (g : 𝕄₄).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).isUnit
    simpa using this
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hg, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hg0 hRdet) hg0
  rw [det_diagonal] at hdet
  have hd : ∀ i, d i ≠ 0 := fun i h => hdet (Finset.prod_eq_zero (Finset.mem_univ i) h)
  have hdd : d = ![d 0, d 1, d 2, d 3] := by
    funext i
    fin_cases i <;> rfl
  have hx := hd 0
  have hy := hd 1
  have hz := hd 2
  have hw := hd 3
  obtain ⟨M, a, c, e, hM, ha, hc, he, hMd⟩ : ∃ (M : 𝕄₄) (a c e : F), M.det ≠ 0 ∧ a ≠ 0 ∧ c ≠ 0 ∧
      e ≠ 0 ∧ Mᵀ * Matrix.diagonal d * M = Matrix.diagonal ![a, a, c, e] := by
    by_cases hxy : IsSquare (d 0 * d 1)
    · obtain ⟨s, hs⟩ := MF15.exists_sq_mul_eq hy hxy
      have hs0 : s ≠ 0 := by
        rintro rfl
        simp at hs
        exact hx hs.symm
      refine ⟨!![1, 0, 0, 0; 0, s, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], d 0, d 2, d 3, ?_, hx, hz, hw, ?_⟩
      · simp [det_succ_row_zero, Fin.sum_univ_succ, hs0]
      · rw [hdd]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
        linear_combination hs
    · by_cases hxz : IsSquare (d 0 * d 2)
      · obtain ⟨s, hs⟩ := MF15.exists_sq_mul_eq hz hxz
        have hs0 : s ≠ 0 := by
          rintro rfl
          simp at hs
          exact hx hs.symm
        refine ⟨!![1, 0, 0, 0; 0, 0, 1, 0; 0, s, 0, 0; 0, 0, 0, 1], d 0, d 1, d 3, ?_, hx, hy, hw,
          ?_⟩
        · simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, hs0]
        · rw [hdd]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
          linear_combination hs
      · have hsq := MF15.isSquare_mul_of_not hxy hxz
        have hyz : IsSquare (d 1 * d 2) := by
          obtain ⟨r, hr⟩ := hsq
          refine ⟨r / d 0, ?_⟩
          field_simp
          linear_combination hr
        obtain ⟨s, hs⟩ := MF15.exists_sq_mul_eq hz hyz
        have hs0 : s ≠ 0 := by
          rintro rfl
          simp at hs
          exact hy hs.symm
        refine ⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, s, 0, 0; 0, 0, 0, 1], d 1, d 0, d 3, ?_, hy, hx, hw,
          ?_⟩
        · simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, hs0]
        · rw [hdd]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
          linear_combination hs
  let Mgl : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero M hM
  refine ⟨g * Mgl, a, c, e, ha, hc, he, ?_⟩
  have hP : ((g * Mgl : GL (Fin 4) F) : 𝕄₄) = (g : 𝕄₄) * M := rfl
  rw [hP, Matrix.transpose_mul, ← hMd, ← hg]
  simp only [Matrix.mul_assoc]

theorem exists_graph_symm [Finite F] (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F)
    (hAt : (A : 𝕄₄)ᵀ = A) :
    ∃ P : GL (Fin 4) F, ((slConjugation 4 F P (rot4 F) : SL(4, F)) : 𝕄₄)ᵀ *
      ((A⁻¹ : GL (Fin 4) F) : 𝕄₄) * ((slConjugation 4 F P (rot4 F) : SL(4, F)) : 𝕄₄) =
        ((A⁻¹ : GL (Fin 4) F) : 𝕄₄) := by
  set R : 𝕄₄ := ((A⁻¹ : GL (Fin 4) F) : 𝕄₄) with hR
  have hAR : (A : 𝕄₄) * R = 1 := by
    rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = R := by
    have h1 : Rᵀ * (A : 𝕄₄)ᵀ = 1 := by
      rw [← transpose_mul, hAR, transpose_one]
    rw [hAt] at h1
    calc Rᵀ = Rᵀ * ((A : 𝕄₄) * R) := by rw [hAR, Matrix.mul_one]
      _ = (Rᵀ * (A : 𝕄₄)) * R := by rw [Matrix.mul_assoc]
      _ = R := by rw [h1, Matrix.one_mul]
  have hRdet : R.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (A⁻¹)).isUnit
    simpa [hR] using this
  obtain ⟨P, a, c, d, -, -, -, hD⟩ := exists_congr_diag_aa4 h2 hRt hRdet
  exact ⟨P, graph_fixed_of_gram P R _ hD (rot4_transpose_mul_diagonal a c d)⟩

theorem colMat_gram (R : 𝕄₄) (v : Fin 4 → Fin 4 → F) (i j : Fin 4) :
    ((colMat v)ᵀ * R * colMat v) i j = v i ⬝ᵥ (R *ᵥ v j) := by
  simp only [colMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem exists_symp_matrix4 (h2 : (2 : F) ≠ 0) {R : 𝕄₄} (hR : Rᵀ = -R) (hRdet : R.det ≠ 0) :
    ∃ P : GL (Fin 4) F, (P : 𝕄₄)ᵀ * R * (P : 𝕄₄) =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  have hBalt : (toBilin' R).IsAlt := fun v => by
    rw [Matrix.toBilin'_apply']
    have hx : v ⬝ᵥ (R *ᵥ v) = -(v ⬝ᵥ (R *ᵥ v)) := by
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hR, neg_mulVec, neg_dotProduct,
        dotProduct_comm]
    have h3 : (2 : F) * (v ⬝ᵥ (R *ᵥ v)) = 0 := by linear_combination hx
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hBnd : (toBilin' R).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 hRdet
  obtain ⟨m, b, hm, hb⟩ := exists_symplectic_basis (toBilin' R) hBalt hBnd
  rw [finrank_fin_fun] at hm
  obtain rfl : m = 2 := by omega
  have hB : ∀ i j, (toBilin' R) (b i) (b j) = Matrix.J (Fin 2) F i j := fun i j => by
    rw [← LinearMap.BilinForm.toMatrix_apply b, hb]
  let v : Fin 4 → Fin 4 → F := ![b (Sum.inr 0), b (Sum.inl 0), b (Sum.inr 1), b (Sum.inl 1)]
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    rcases i with i | i
    · fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · fin_cases i
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
  refine ⟨colGL v hspan, ?_⟩
  rw [coe_colGL]
  ext i j
  rw [colMat_gram]
  have hv : ∀ i j, v i ⬝ᵥ (R *ᵥ v j) = (toBilin' R) (v i) (v j) := fun i j => by
    rw [Matrix.toBilin'_apply']
  rw [hv]
  fin_cases i <;> fin_cases j <;>
    simp [v, hB, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem exists_graph_alt (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F) (hAt : (A : 𝕄₄)ᵀ = -A) :
    ∃ P : GL (Fin 4) F, ((slConjugation 4 F P (rot4 F) : SL(4, F)) : 𝕄₄)ᵀ *
      ((A⁻¹ : GL (Fin 4) F) : 𝕄₄) * ((slConjugation 4 F P (rot4 F) : SL(4, F)) : 𝕄₄) =
        ((A⁻¹ : GL (Fin 4) F) : 𝕄₄) := by
  set R : 𝕄₄ := ((A⁻¹ : GL (Fin 4) F) : 𝕄₄) with hR
  have hAR : (A : 𝕄₄) * R = 1 := by
    rw [hR, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : 𝕄₄)ᵀ = 1 := by
      rw [← transpose_mul, hAR, transpose_one]
    rw [hAt, Matrix.mul_neg, neg_eq_iff_eq_neg] at h1
    calc Rᵀ = Rᵀ * ((A : 𝕄₄) * R) := by rw [hAR, Matrix.mul_one]
      _ = -R := by rw [← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
  have hRdet : R.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (A⁻¹)).isUnit
    simpa [hR] using this
  obtain ⟨P, hP⟩ := exists_symp_matrix4 h2 hRt hRdet
  exact ⟨P, graph_fixed_of_gram P R _ hP rot4_transpose_mul_symp⟩

end CFSG.ClassicalInvolution.ModelFacts.L6C
