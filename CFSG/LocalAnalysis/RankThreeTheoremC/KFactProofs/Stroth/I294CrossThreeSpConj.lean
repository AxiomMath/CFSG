module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeSpAdapted
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeSpBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open Matrix Module CFSG.Open
open LinearMap (BilinForm)

namespace Sp6

section Conj

variable {K : Type} [Field K]

theorem fromBlocks_eq_neg_J :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = -Matrix.J (Fin 3) K := by
  simp [Matrix.J, fromBlocks_neg]

theorem mem_statedSp_iff_J {g : GL (Fin 3 ⊕ Fin 3) K} :
    g ∈ StatedSp 3 K ↔ (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)ᵀ * Matrix.J (Fin 3) K *
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = Matrix.J (Fin 3) K := by
  rw [StatedAPI.mem_statedSp_iff, fromBlocks_eq_neg_J, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

@[expose] noncomputable def jForm (K : Type) [Field K] : BilinForm K (Fin 3 ⊕ Fin 3 → K) :=
  Matrix.toBilin' (Matrix.J (Fin 3) K)

theorem jForm_isAlt : (jForm K).IsAlt := by
  intro x
  simp [jForm, Matrix.toBilin'_apply', Matrix.J, dotProduct, Fintype.sum_sum_type,
    fromBlocks_mulVec, Matrix.neg_mulVec, mul_comm]

theorem jForm_nondegenerate : (jForm K).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _
    (Matrix.isUnit_det_J (Fin 3) K).ne_zero

theorem matrix_of_basis_mem_J (b : Basis (Fin 3 ⊕ Fin 3) K (Fin 3 ⊕ Fin 3 → K))
    (hb : ∀ x y, jForm K (b x) (b y) = Matrix.J (Fin 3) K x y) :
    (Matrix.of fun r c => b c r)ᵀ * Matrix.J (Fin 3) K * (Matrix.of fun r c => b c r) =
      Matrix.J (Fin 3) K := by
  set P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K := Matrix.of fun r c => b c r with hP
  have hcol : ∀ c, P *ᵥ Pi.single c 1 = b c := fun c => by
    ext r
    simp [hP, Matrix.mulVec_single_one]
  ext x y
  have h1 := hb x y
  rw [← hcol x, ← hcol y] at h1
  have h2 := congrArg (fun B => B (Pi.single x 1) (Pi.single y 1))
    (Matrix.toBilin'_comp (Matrix.J (Fin 3) K) P P)
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toBilin'_single, Matrix.toLin'_apply] at h2
  rw [← h2]
  exact h1

theorem exists_conj_blkGL (h3 : (3 : K) ≠ 0) (g : GL (Fin 3 ⊕ Fin 3) K) (hg : g ∈ StatedSp 3 K)
    (hg3 : g ^ 3 = 1) :
    ∃ P : GL (Fin 3 ⊕ Fin 3) K, P ∈ StatedSp 3 K ∧
      ∃ M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K, g = P * blkGL M * P⁻¹ := by
  set gm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with hgm
  have hgJ : gmᵀ * Matrix.J (Fin 3) K * gm = Matrix.J (Fin 3) K := mem_statedSp_iff_J.1 hg
  have hgm3 : gm * (gm * gm) = 1 := by
    have := congrArg (fun h : GL (Fin 3 ⊕ Fin 3) K =>
      (h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) hg3
    simpa [pow_succ, Units.val_mul, hgm, mul_assoc] using this
  set gl : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) := Matrix.toLin' gm with hgl
  have hiso : ∀ x y, jForm K (gl x) (gl y) = jForm K x y := by
    intro x y
    have h := congrArg (fun B => B x y) (Matrix.toBilin'_comp (Matrix.J (Fin 3) K) gm gm)
    simp only [LinearMap.BilinForm.comp_apply, hgJ] at h
    exact h
  have hgl3 : ∀ x, gl (gl (gl x)) = x := by
    intro x
    simp only [hgl, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
    rw [hgm3, Matrix.one_mulVec]
  obtain ⟨m, b, hb, hadapt⟩ := exists_adapted_symplectic_basis h3 _ (Fin 3 ⊕ Fin 3 → K) rfl
    (jForm K) jForm_isAlt jForm_nondegenerate gl hiso hgl3
  have hm : m = 3 := by
    have h := Module.finrank_eq_card_basis b
    simp at h
    omega
  subst hm
  set P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K := Matrix.of fun r c => b c r with hP
  have hPJ : Pᵀ * Matrix.J (Fin 3) K * P = Matrix.J (Fin 3) K := matrix_of_basis_mem_J b hb
  have hPunit : IsUnit P.det := by
    have hPe : P = (Pi.basisFun K (Fin 3 ⊕ Fin 3)).toMatrix b := by
      ext r c
      simp [hP, Basis.toMatrix_apply]
    rw [hPe, ← Matrix.isUnit_iff_isUnit_det]
    exact @isUnit_of_invertible _ _ _ ((Pi.basisFun K (Fin 3 ⊕ Fin 3)).invertibleToMatrix b)
  set Pg : GL (Fin 3 ⊕ Fin 3) K := Matrix.GeneralLinearGroup.mk'' P hPunit with hPg
  have hPgval : (Pg : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = P := rfl
  have hPsp : Pg ∈ StatedSp 3 K := mem_statedSp_iff_J.2 (by rw [hPgval]; exact hPJ)
  choose s t u v h1 h2 using hadapt
  set M' : Fin 3 → Matrix (Fin 2) (Fin 2) K := fun i => !![s i, u i; t i, v i] with hM'
  have hrel : gm * P = P * blkMat M' := by
    ext r c
    rcases c with i | i
    · have e1 : (gm * P) r (Sum.inl i) = (gl (b (Sum.inl i))) r := by
        simp [Matrix.mul_apply, hgl, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hP]
      have e2 : (P * blkMat M') r (Sum.inl i) =
          (s i • b (Sum.inl i) + t i • b (Sum.inr i)) r := by
        simp [Matrix.mul_apply, Fintype.sum_sum_type, blkMat, hP, Matrix.diagonal_apply, hM',
          mul_comm]
      rw [e1, e2, h1 i]
    · have e1 : (gm * P) r (Sum.inr i) = (gl (b (Sum.inr i))) r := by
        simp [Matrix.mul_apply, hgl, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hP]
      have e2 : (P * blkMat M') r (Sum.inr i) =
          (u i • b (Sum.inl i) + v i • b (Sum.inr i)) r := by
        simp [Matrix.mul_apply, Fintype.sum_sum_type, blkMat, hP, Matrix.diagonal_apply, hM',
          mul_comm]
      rw [e1, e2, h2 i]
  have hdet : ∀ i, (M' i).det = 1 := by
    intro i
    have h := hiso (b (Sum.inl i)) (b (Sum.inr i))
    rw [h1 i, h2 i] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb] at h
    simp [Matrix.J, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂] at h
    simp [hM', Matrix.det_fin_two_of]
    linear_combination (-1 : K) * h
  let M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K := fun i => ⟨M' i, hdet i⟩
  refine ⟨Pg, hPsp, M, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL, hPgval]
  exact hrel

end Conj

end Sp6

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
