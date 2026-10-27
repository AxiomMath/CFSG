module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3Mon
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddTorus

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] (σ : F ≃+* F)

section Frame

@[expose] def frameMat (c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, c, 0; 0, 0, 1; (2 : F)⁻¹, -(c * (2 : F)⁻¹), 0]

theorem conjTr_antidiag3 (hσ : ∀ x, σ (σ x) = x) : conjTr σ (antidiag 3 : Matrix (Fin 3) (Fin 3) F) =
    antidiag 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, antidiag]

theorem antidiag3_mul_self : (antidiag 3 : Matrix (Fin 3) (Fin 3) F) * antidiag 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, Matrix.mul_apply, Fin.sum_univ_three]

theorem conjTr_conjTr (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin 3) (Fin 3) F) :
    conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hσ]

theorem frameMat_isometry (h2 : (2 : F) ≠ 0) (hσ2 : σ 2 = 2) {c : F} (hc : σ c * c = -1) :
    conjTr σ (frameMat c) * antidiag 3 * frameMat c = 1 := by
  have hi : σ (2 : F)⁻¹ = (2 : F)⁻¹ := by rw [map_inv₀, hσ2]
  have h22 : (2 : F)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, antidiag, frameMat, Matrix.mul_apply, Fin.sum_univ_three, hi]
  · exact h22
  · ring
  · linear_combination (-1 : F) * hc + (-(σ c * c)) * h22

@[expose] noncomputable def frameGL (c : F)
    (h : conjTr σ (frameMat c) * antidiag 3 * frameMat c = 1) : GL (Fin 3) F :=
  ⟨frameMat c, conjTr σ (frameMat c) * antidiag 3, mul_eq_one_comm.1 h, h⟩

theorem coe_frameGL (c : F) (h : conjTr σ (frameMat c) * antidiag 3 * frameMat c = 1) :
    ((frameGL σ c h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = frameMat c := rfl

theorem coe_frameGL_inv (c : F) (h : conjTr σ (frameMat c) * antidiag 3 * frameMat c = 1) :
    (((frameGL σ c h)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      conjTr σ (frameMat c) * antidiag 3 := rfl

theorem frameGL_inv_isometry (hσ : ∀ x, σ (σ x) = x) (c : F)
    (h : conjTr σ (frameMat c) * antidiag 3 * frameMat c = 1) :
    conjTr σ (((frameGL σ c h)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (((frameGL σ c h)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = antidiag 3 := by
  rw [coe_frameGL_inv]
  set M := frameMat c
  set J : Matrix (Fin 3) (Fin 3) F := antidiag 3
  have hJJ : J * J = 1 := antidiag3_mul_self
  have hJt : conjTr σ J = J := conjTr_antidiag3 σ hσ
  have hMM : M * conjTr σ M = J := by
    have h1 : M * (conjTr σ M * J) = 1 := mul_eq_one_comm.1 h
    calc M * conjTr σ M = M * conjTr σ M * (J * J) := by rw [hJJ, Matrix.mul_one]
      _ = (M * (conjTr σ M * J)) * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, Matrix.one_mul]
  rw [conjTr_mul, conjTr_conjTr σ hσ, hJt]
  calc J * M * (conjTr σ M * J) = J * (M * conjTr σ M) * J := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hMM, hJJ, Matrix.one_mul]

variable {p f : ℕ} [Fact p.Prime] [CharP F p] [Finite F]

@[expose] noncomputable def frameEquiv (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) {c : F}
    (hc : unitaryInvolution F p f c * c = -1) :
    SU (unitaryInvolution F p f) 3 ≃* SUid (unitaryInvolution F p f) 3 :=
  conjEquiv (frameGL (unitaryInvolution F p f) c
    (frameMat_isometry _ h2 (map_ofNat _ 2) hc))⁻¹
    (frameGL_inv_isometry _ (unitaryInvolution_involutive hF) c _)

theorem coe_frameEquiv (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) {c : F}
    (hc : unitaryInvolution F p f c * c = -1) (A : SU (unitaryInvolution F p f) 3) :
    ((frameEquiv hF h2 hc A : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) =
      (frameGL (unitaryInvolution F p f) c (frameMat_isometry _ h2 (map_ofNat _ 2) hc))⁻¹ * A *
        frameGL (unitaryInvolution F p f) c (frameMat_isometry _ h2 (map_ofNat _ 2) hc) := by
  rw [frameEquiv, coe_conjEquiv, inv_inv]

section Torus

variable (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) {c : F}
  (hc : unitaryInvolution F p f c * c = -1)

theorem tMat_eq_of_norm_eq_one (l : Fˣ) (hl : unitaryInvolution F p f (l : F) * l = 1) :
    tMat (p ^ f) l = Matrix.diagonal ![(l : F), (((l * l)⁻¹ : Fˣ) : F), (l : F)] := by
  have hq : 1 ≤ p ^ f := one_le_prime_pow p f
  have h1 : l ^ (p ^ f) * l = 1 := by
    apply Units.ext
    rw [unitaryInvolution_apply] at hl
    simpa using hl
  have e2 : (l ^ (p ^ f))⁻¹ = l := inv_eq_of_mul_eq_one_right h1
  have e1 : l ^ (p ^ f - 1) = (l * l)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have : l ^ (p ^ f) = l ^ (p ^ f - 1) * l := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    rw [← mul_assoc, ← this]
    exact h1
  unfold tMat
  rw [e1, e2]

theorem tSU_mul_frame (l : Fˣ) (hl : unitaryInvolution F p f (l : F) * l = 1) :
    (tSU hF l : GL (Fin 3) F) *
        frameGL (unitaryInvolution F p f) c (frameMat_isometry _ h2 (map_ofNat _ 2) hc) =
      frameGL (unitaryInvolution F p f) c (frameMat_isometry _ h2 (map_ofNat _ 2) hc) *
        dGL l l (l * l)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_frameGL, coe_dGL]
  change tMat (p ^ f) l * frameMat c = frameMat c * dMat (l : F) (l : F) (((l * l)⁻¹ : Fˣ) : F)
  rw [tMat_eq_of_norm_eq_one l hl]
  have hl0 := l.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameMat, dMat, Matrix.mul_apply, Fin.sum_univ_three, Units.val_inv_eq_inv_val]
  all_goals ring

theorem frameEquiv_tSU (l : Fˣ) (hl : unitaryInvolution F p f (l : F) * l = 1) :
    ((frameEquiv hF h2 hc (tSU hF l) : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) =
      dGL l l (l * l)⁻¹ := by
  rw [coe_frameEquiv, mul_assoc, tSU_mul_frame hF h2 hc l hl]
  group

end Torus

end Frame

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
