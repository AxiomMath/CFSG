module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuMix
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.AscE189Model
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Std
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuSlayer
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (SLayer)
open scoped MatrixGroups

section Alg

variable {K : Type} [Field K]

@[expose] def Yp (ω : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1 - ω, 0, 1 - ω, 0; 1 + ω, 0, -(1 + ω), 0; 0, 1 - ω, 0, -(1 - ω); 0, 1 + ω, 0, 1 + ω]

@[expose] def Yb (ω : K) : Matrix (Fin 4) (Fin 4) K := (2 : K)⁻¹ • Yp ω

variable {ω : K}

local macro "om_solve" hω:term : tactic =>
  `(tactic| first
    | ring1
    | linear_combination ($hω)
    | linear_combination (-1) * $hω
    | linear_combination 2 * $hω
    | linear_combination (-2) * $hω
    | linear_combination 4 * $hω
    | linear_combination (-4) * $hω
    | linear_combination 8 * $hω
    | linear_combination (-8) * $hω)

theorem conjTr_Yp_mul (σ : K ≃+* K) (hω : ω * ω = -1) (hσω : σ ω = -ω) :
    conjTr σ (Yp ω) * Yp ω = (4 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Yp, Matrix.mul_apply, Fin.sum_univ_four, hσω] <;> om_solve hω

theorem det_Yp (hω : ω * ω = -1) : (Yp ω).det = 16 := by
  simp [Yp, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (4 * ω ^ 2 - 12) * hω

theorem Yp_mul_x0 (hω : ω * ω = -1) :
    Yp ω * (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) =
      (ω • (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : Matrix (Fin 4) (Fin 4) K)) *
        Yp ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Yp, Matrix.mul_apply, Fin.sum_univ_four] <;> om_solve hω

theorem Yp_mul_t0 (hω : ω * ω = -1) :
    Yp ω * (!![-ω, 0, 0, 0; 0, ω, 0, 0; 0, 0, ω, 0; 0, 0, 0, -ω] : Matrix (Fin 4) (Fin 4) K) =
      ((!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) *
        !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]) * Yp ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Yp, Matrix.mul_apply, Fin.sum_univ_four] <;> om_solve hω

theorem diag4_mul_Yp (s w : K) :
    diag4 s w * Yp ω = Yp ω * Matrix.diagonal ![s, w, s, w] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4, Yp, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem conjTr_smul (σ : K ≃+* K) (c : K) (M : Matrix (Fin 4) (Fin 4) K) :
    conjTr σ (c • M) = σ c • conjTr σ M := by
  ext i j
  simp [conjTr]

theorem two_inv_fixed (σ : K ≃+* K) : σ (2 : K)⁻¹ = (2 : K)⁻¹ := by
  rw [map_inv₀, map_ofNat]

theorem conjTr_Yb_mul (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1) (hσω : σ ω = -ω) :
    conjTr σ (Yb ω) * Yb ω = 1 := by
  rw [Yb, conjTr_smul, two_inv_fixed, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    conjTr_Yp_mul σ hω hσω, smul_smul]
  have : (2 : K)⁻¹ * (2 : K)⁻¹ * 4 = 1 := by
    field_simp
    norm_num
  rw [this, one_smul]

theorem det_Yb (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1) : (Yb ω).det = 1 := by
  rw [Yb, Matrix.det_smul, det_Yp hω]
  simp only [Fintype.card_fin]
  field_simp
  norm_num

end Alg

section GroupB

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {ω : K}

@[expose] noncomputable def zOm (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    Su K p f 4 :=
  mkSU K p f (ω • (1 : Matrix (Fin 4) (Fin 4) K))
    (by
      rw [Matrix.det_smul, Matrix.det_one]
      simp only [Fintype.card_fin, mul_one]
      linear_combination (ω * ω - 1) * hω)
    (by
      rw [conjTr_smul, conjTr_one, hσω, Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul]
      have : -ω * ω = 1 := by linear_combination (-1) * hω
      rw [this, one_smul])

theorem suMat_zOm (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    suMat (zOm hω hσω) = ω • (1 : Matrix (Fin 4) (Fin 4) K) := rfl

theorem zOm_mem_center (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    zOm hω hσω ∈ Subgroup.center (Su K p f 4) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_zOm]
  simp

@[expose] noncomputable def yB (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1)
    (hσω : unitaryInvolution K p f ω = -ω) : Su K p f 4 :=
  mkSU K p f (Yb ω) (det_Yb h2 hω) (conjTr_Yb_mul _ h2 hω hσω)

theorem suMat_yB (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    suMat (yB h2 hω hσω) = Yb ω := rfl

theorem yB_mul_x0 (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    yB h2 hω hσω * x0 K p f = (zOm hω hσω * u0 K p f) * yB h2 hω hσω := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_mul, suMat_yB, suMat_zOm, suMat_x0, suMat_u0, Yb]
  have key := Yp_mul_x0 hω
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, key, smul_smul]

theorem yB_conj_x0 (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1)
    (hσω : unitaryInvolution K p f ω = -ω) :
    yB h2 hω hσω * x0 K p f * (yB h2 hω hσω)⁻¹ = zOm hω hσω * u0 K p f := by
  rw [mul_inv_eq_iff_eq_mul, yB_mul_x0]

theorem dSU_neg_data (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    unitaryInvolution K p f (-ω) * (-ω) = 1 ∧
      unitaryInvolution K p f (unitaryInvolution K p f (-ω)) = -ω := by
  have hσ : unitaryInvolution K p f (-ω) = ω := by rw [map_neg, hσω, neg_neg]
  refine ⟨?_, ?_⟩
  · rw [hσ]
    linear_combination (-1) * hω
  · rw [hσ, hσω]

theorem dSU_pos_data (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    unitaryInvolution K p f ω * ω = 1 ∧
      unitaryInvolution K p f (unitaryInvolution K p f ω) = ω := by
  refine ⟨?_, ?_⟩
  · rw [hσω]
    linear_combination (-1) * hω
  · rw [hσω, map_neg, hσω, neg_neg]

@[expose] noncomputable def tDiag (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    Su K p f 4 :=
  blk K p f (dSU K p f (dSU_neg_data hω hσω).1 (dSU_neg_data hω hσω).2)
    (dSU K p f (dSU_pos_data hω hσω).1 (dSU_pos_data hω hσω).2)

theorem suMat_tDiag (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    suMat (tDiag hω hσω) =
      (!![-ω, 0, 0, 0; 0, ω, 0, 0; 0, 0, ω, 0; 0, 0, 0, -ω] : Matrix (Fin 4) (Fin 4) K) := by
  rw [tDiag, suMat_blk, suMat_dSU, suMat_dSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [map_neg, hσω]

theorem yB_mul_tDiag (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1)
    (hσω : unitaryInvolution K p f ω = -ω) :
    yB h2 hω hσω * tDiag hω hσω = t0 K p f * yB h2 hω hσω := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_yB, suMat_tDiag, t0, suMat_mul, suMat_x0, suMat_u0, Yb]
  have key := Yp_mul_t0 hω
  simp only [Matrix.smul_mul, Matrix.mul_smul, key]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem h0_blk_j : ∀ s w : K, s ≠ 0 → w ≠ 0 → ∀ z : K,
    Matrix.diagonal ![s, w, s, w] *
        (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) =
      z • ((!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) *
        Matrix.diagonal ![s, w, s, w]) → s = w := by
  intro s w hs hw z h
  have e22 := congrFun (congrFun h 2) 2
  have e01 := congrFun (congrFun h 0) 1
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at e22 e01
  simp at e22 e01
  have hz : z = 1 := by
    have h1 : s * (1 - z) = 0 := by linear_combination e22
    have h3 := (mul_eq_zero.mp h1).resolve_left hs
    linear_combination -h3
  rw [hz] at e01
  linear_combination e01

theorem suMat_blk_j_one : suMat (blk K p f (jSU K p f) 1) =
    (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) := by
  rw [suMat_blk, suMat_jSU, suMat_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_layer_u0_of_neg (hK : Nat.card K = (p ^ f) ^ 2) (h2 : (2 : K) ≠ 0)
    (hq : 5 ≤ p ^ f) (hω : ω * ω = -1) (hσω : unitaryInvolution K p f ω = -ω) :
    ∃ Q : Subgroup (Su K p f 4), SLayer (u0 K p f) Q ∧ t0 K p f ∈ Q ∧
      ∃ m ∈ Q, MixProp (suMat m) := by
  set y := yB h2 hω hσω with hy
  refine ⟨(R0 K p f ⊔ R0' K p f).map (MulAut.conj y).toMonoidHom, ?_, ?_, ?_⟩
  · have h1 := (slayer_x0 hK h2 hq).map (MulAut.conj y)
    have e : (MulAut.conj y) (x0 K p f) = zOm hω hσω * u0 K p f := yB_conj_x0 h2 hω hσω
    rw [e] at h1
    have h2' := h1.of_central_mul (Subgroup.inv_mem _ (zOm_mem_center hω hσω))
    rwa [inv_mul_cancel_left] at h2'
  · refine ⟨tDiag hω hσω, blk_mem _ _, ?_⟩
    show y * tDiag hω hσω * y⁻¹ = t0 K p f
    rw [mul_inv_eq_iff_eq_mul, yB_mul_tDiag]
  · refine ⟨y * blk K p f (jSU K p f) 1 * y⁻¹, ⟨blk K p f (jSU K p f) 1, blk_mem _ _, rfl⟩, ?_⟩
    refine mixProp_of_conj (Y := Yb ω) (Yi := suMat y⁻¹)
      (M₀ := suMat (blk K p f (jSU K p f) 1)) ?_ ?_ ?_ ?_
    · exact suMat_inv_mul_suMat y
    · intro s w
      rw [Yb, Matrix.mul_smul, Matrix.smul_mul, diag4_mul_Yp]
    · have e1 : suMat (y * blk K p f (jSU K p f) 1 * y⁻¹) * Yb ω =
          suMat (y * blk K p f (jSU K p f) 1 * y⁻¹ * y) := by
        rw [suMat_mul]
        rfl
      rw [e1, inv_mul_cancel_right, suMat_mul]
      rfl
    · rw [suMat_blk_j_one]
      exact h0_blk_j

end GroupB

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
