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

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

section Lev

variable {K : Type} [Field K]

@[expose] def Lev (A B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

@[expose] def Gam : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem Lev_mul (A B C D : Matrix (Fin 2) (Fin 2) K) :
    Lev A B * Lev C D = Lev (A * C) (B * D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lev, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem Lev_one : Lev (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lev]

theorem conjTr_Lev (σ : K ≃+* K) (A B : Matrix (Fin 2) (Fin 2) K) :
    conjTr σ (Lev A B) = Lev (conjTr σ A) (conjTr σ B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lev, conjTr]

theorem det_Lev (A B : Matrix (Fin 2) (Fin 2) K) : (Lev A B).det = A.det * B.det := by
  rw [Lev, det_blockDiag4, Matrix.det_fin_two, Matrix.det_fin_two]

theorem Gam_Lev (A B : Matrix (Fin 2) (Fin 2) K) : Gam * Lev A B = Lev B A * Gam := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gam, Lev, Matrix.mul_apply, Fin.sum_univ_four]

theorem Gam_mul_Gam : (Gam : Matrix (Fin 4) (Fin 4) K) * Gam = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gam, Matrix.mul_apply, Fin.sum_univ_four]

theorem conjTr_Gam (σ : K ≃+* K) : conjTr σ (Gam : Matrix (Fin 4) (Fin 4) K) = Gam := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gam, conjTr]

theorem det_Gam : (Gam : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [Gam, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem Lev_inj {A B A' B' : Matrix (Fin 2) (Fin 2) K} (h : Lev A B = Lev A' B') :
    A = A' ∧ B = B' := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  have g00 := congrFun (congrFun h 2) 2
  have g01 := congrFun (congrFun h 2) 3
  have g10 := congrFun (congrFun h 3) 2
  have g11 := congrFun (congrFun h 3) 3
  simp [Lev] at h00 h01 h10 h11 g00 g01 g10 g11
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> assumption
  · ext i j
    fin_cases i <;> fin_cases j <;> assumption

theorem eq_Lev_of_comm {M : Matrix (Fin 4) (Fin 4) K} {a b : K} (hab : a ≠ b)
    (h : M * Matrix.diagonal ![a, a, b, b] = Matrix.diagonal ![a, a, b, b] * M) :
    ∃ A B : Matrix (Fin 2) (Fin 2) K, M = Lev A B := by
  have key : ∀ i j : Fin 4, M i j * ![a, a, b, b] j = ![a, a, b, b] i * M i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hz : ∀ x : K, x * (a - b) = 0 → x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_right (sub_ne_zero.mpr hab)
  have m02 : M 0 2 = 0 := hz _ (by have := key 0 2; simp at this; linear_combination -this)
  have m03 : M 0 3 = 0 := hz _ (by have := key 0 3; simp at this; linear_combination -this)
  have m12 : M 1 2 = 0 := hz _ (by have := key 1 2; simp at this; linear_combination -this)
  have m13 : M 1 3 = 0 := hz _ (by have := key 1 3; simp at this; linear_combination -this)
  have m20 : M 2 0 = 0 := hz _ (by have := key 2 0; simp at this; linear_combination this)
  have m21 : M 2 1 = 0 := hz _ (by have := key 2 1; simp at this; linear_combination this)
  have m30 : M 3 0 = 0 := hz _ (by have := key 3 0; simp at this; linear_combination this)
  have m31 : M 3 1 = 0 := hz _ (by have := key 3 1; simp at this; linear_combination this)
  refine ⟨!![M 0 0, M 0 1; M 1 0, M 1 1], !![M 2 2, M 2 3; M 3 2, M 3 3], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lev, m02, m03, m12, m13, m20, m21, m30, m31]

end Lev

section Ya

variable {K : Type} [Field K] {ω : K}

@[expose] def Ya (ω : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 1, 0; ω, 0, -ω, 0; 0, 1, 0, 1; 0, ω, 0, -ω]

@[expose] def Yai (ω : K) : Matrix (Fin 4) (Fin 4) K :=
  (2 : K)⁻¹ • !![1, -ω, 0, 0; 0, 0, 1, -ω; 1, ω, 0, 0; 0, 0, 1, ω]

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

theorem conjTr_Ya_mul (σ : K ≃+* K) (hω : ω * ω = -1) (hσω : σ ω = ω) :
    conjTr σ (Ya ω) * Ya ω = (2 : K) • (Gam : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Ya, Gam, Matrix.mul_apply, Fin.sum_univ_four, hσω] <;> om_solve hω

theorem Yai_mul_Ya (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1) : Yai ω * Ya ω = 1 := by
  have key : (!![1, -ω, 0, 0; 0, 0, 1, -ω; 1, ω, 0, 0; 0, 0, 1, ω] : Matrix (Fin 4) (Fin 4) K) *
      Ya ω = (2 : K) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ya, Matrix.mul_apply, Fin.sum_univ_four] <;> om_solve hω
  rw [Yai, Matrix.smul_mul, key, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem Ya_mul_Yai (h2 : (2 : K) ≠ 0) (hω : ω * ω = -1) : Ya ω * Yai ω = 1 :=
  mul_eq_one_comm.mp (Yai_mul_Ya h2 hω)

theorem U0_mul_Ya (hω : ω * ω = -1) :
    (!![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] : Matrix (Fin 4) (Fin 4) K) * Ya ω =
      Ya ω * Matrix.diagonal ![ω, ω, -ω, -ω] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ya, Matrix.mul_apply, Fin.sum_univ_four] <;> om_solve hω

theorem T0_mul_Ya (hω : ω * ω = -1) :
    ((!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) *
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]) * Ya ω =
      Ya ω * Matrix.diagonal ![-ω, ω, ω, -ω] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ya, Matrix.mul_apply, Fin.sum_univ_four] <;> om_solve hω

theorem diag4_mul_Ya (s w : K) :
    diag4 s w * Ya ω = Ya ω * Matrix.diagonal ![s, w, s, w] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag4, Ya, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

variable {σ : K ≃+* K}

theorem unitary_conj (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) {Y Yi L : Matrix (Fin 4) (Fin 4) K}
    (hYYi : Y * Yi = 1) (hY : conjTr σ Y * Y = (2 : K) • Gam)
    (hL : conjTr σ L * Gam * L = Gam) : conjTr σ (Y * L * Yi) * (Y * L * Yi) = 1 := by
  have hΓ : (Gam : Matrix (Fin 4) (Fin 4) K) = (2 : K)⁻¹ • (conjTr σ Y * Y) := by
    rw [hY, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have h1 : conjTr σ Yi * Gam * Yi = (2 : K)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [hΓ]
    calc conjTr σ Yi * ((2 : K)⁻¹ • (conjTr σ Y * Y)) * Yi
        = (2 : K)⁻¹ • (conjTr σ Yi * conjTr σ Y * (Y * Yi)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = (2 : K)⁻¹ • (conjTr σ (Y * Yi) * (Y * Yi)) := by rw [conjTr_mul]
      _ = (2 : K)⁻¹ • 1 := by rw [hYYi, conjTr_one, Matrix.one_mul]
  calc conjTr σ (Y * L * Yi) * (Y * L * Yi)
      = conjTr σ Yi * conjTr σ L * (conjTr σ Y * Y) * L * Yi := by
        rw [conjTr_mul, conjTr_mul]
        simp only [Matrix.mul_assoc]
    _ = (2 : K) • (conjTr σ Yi * (conjTr σ L * Gam * L) * Yi) := by
        rw [hY]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = (2 : K) • (conjTr σ Yi * Gam * Yi) := by rw [hL]
    _ = 1 := by rw [h1, smul_smul, mul_inv_cancel₀ h2, one_smul]

theorem det_conj {Y Yi L : Matrix (Fin 4) (Fin 4) K} (hYYi : Y * Yi = 1) :
    (Y * L * Yi).det = L.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Y.det) L.det, mul_assoc, ← Matrix.det_mul, hYYi,
    Matrix.det_one, mul_one]

theorem conjTr_Yi_Gam_Yi (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) {Y Yi : Matrix (Fin 4) (Fin 4) K}
    (hYYi : Y * Yi = 1) (hY : conjTr σ Y * Y = (2 : K) • Gam) :
    conjTr σ Yi * Gam * Yi = (2 : K)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) K) := by
  have hΓ : (Gam : Matrix (Fin 4) (Fin 4) K) = (2 : K)⁻¹ • (conjTr σ Y * Y) := by
    rw [hY, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hΓ]
  calc conjTr σ Yi * ((2 : K)⁻¹ • (conjTr σ Y * Y)) * Yi
      = (2 : K)⁻¹ • (conjTr σ Yi * conjTr σ Y * (Y * Yi)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = (2 : K)⁻¹ • (conjTr σ (Y * Yi) * (Y * Yi)) := by rw [conjTr_mul]
    _ = (2 : K)⁻¹ • 1 := by rw [hYYi, conjTr_one, Matrix.one_mul]

theorem unitary_conj_inv (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) {Y Yi G : Matrix (Fin 4) (Fin 4) K}
    (hYYi : Y * Yi = 1) (hY : conjTr σ Y * Y = (2 : K) • Gam) (hG : conjTr σ G * G = 1) :
    conjTr σ (Yi * G * Y) * Gam * (Yi * G * Y) = Gam := by
  have h1 := conjTr_Yi_Gam_Yi σ h2 hYYi hY
  calc conjTr σ (Yi * G * Y) * Gam * (Yi * G * Y)
      = conjTr σ Y * conjTr σ G * (conjTr σ Yi * Gam * Yi) * G * Y := by
        rw [conjTr_mul, conjTr_mul]
        simp only [Matrix.mul_assoc]
    _ = (2 : K)⁻¹ • (conjTr σ Y * (conjTr σ G * G) * Y) := by
        rw [h1]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_one]
    _ = Gam := by
        rw [hG, Matrix.mul_one, hY, smul_smul, inv_mul_cancel₀ h2, one_smul]

end Ya

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
