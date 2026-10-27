module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProj
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat
  conj_injective_of_mulEquiv eq_bot_of_oddCoreIn)

variable {K : Type} [Field K] {d : ℕ}

theorem socleAction_trans {X : Type} [Group X] {T T' : Type*} [Group T] [Group T']
    (θ : GeneralizedFitting.subgroup X ≃* T) (Θ : T ≃* T') (x : X) :
    socleAction (θ.trans Θ) x = MulAut.congr Θ (socleAction θ x) := rfl

theorem propAConclusion_of_socle {X : Type} [Group X] [Finite X] {T : Type} [Group T]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    (θ : GeneralizedFitting.subgroup X ≃* T) {t : X} {Y : Subgroup X} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t)
    (h : oddCoreIn (socleAction θ).range (socleAction θ t) = ⊥ ∨
      ∀ Y' : Subgroup (MulAut T), Y' ≠ ⊥ →
        Y' ≤ oddCoreIn (socleAction θ).range (socleAction θ t) →
        PropAConclusionIn (socleAction θ).range (socleAction θ t) Y') :
    PropAConclusion X t Y := by
  have hψ := socleAction_injective hsimple hnab θ
  rcases h with h | h
  · exact absurd (eq_bot_of_oddCoreIn hψ h hYO) hY
  · apply PropAConclusion.of_injective hψ
    refine h _ (fun hmap => hY ((map_eq_bot_iff_of_injective _ hψ).1 hmap)) ?_
    rw [← map_oddCentralizerCore_of_injective hψ]
    exact map_mono hYO

theorem exists_isometric_involution (hdodd : Odd d) {R : GL (Fin d) K} {A : GL (Fin d) K}
    {μ : K}
    (hμ : (A : Matrix (Fin d) (Fin d) K)ᵀ * R * A = μ • (R : Matrix (Fin d) (Fin d) K))
    {c : Kˣ} (hc : A * A = GeneralLinearGroup.scalar (Fin d) c) :
    ∃ m : K, m ≠ 0 ∧ (m⁻¹ • (A : Matrix (Fin d) (Fin d) K))ᵀ * R *
        (m⁻¹ • (A : Matrix (Fin d) (Fin d) K)) = R ∧
      (m⁻¹ • (A : Matrix (Fin d) (Fin d) K)) * (m⁻¹ • (A : Matrix (Fin d) (Fin d) K)) = 1 := by
  obtain ⟨k, hk⟩ := hdodd
  set Am := (A : Matrix (Fin d) (Fin d) K) with hAm
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hdA : Am.det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hdR : Rm.det ≠ 0 := (Matrix.isUnits_det_units R).ne_zero
  have hdet : Am.det ^ 2 = μ ^ d := by
    have e := congrArg Matrix.det hμ
    rw [det_mul, det_mul, det_transpose, det_smul, Fintype.card_fin] at e
    have : (Am.det ^ 2 - μ ^ d) * Rm.det = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hdR)
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hdet
    exact hdA (pow_eq_zero_iff (by norm_num) |>.1 hdet)
  set m0 := Am.det / μ ^ k with hm0
  have hm00 : m0 ≠ 0 := div_ne_zero hdA (pow_ne_zero _ hμ0)
  have hm2 : m0 ^ 2 = μ := by
    rw [hm0, div_pow, hdet, hk, ← pow_mul, pow_succ]
    field_simp
    ring
  have hA'R : (m0⁻¹ • Am)ᵀ * Rm * (m0⁻¹ • Am) = Rm := by
    rw [show (m0⁻¹ • Am)ᵀ * Rm * (m0⁻¹ • Am) = (m0⁻¹ * m0⁻¹) • (Amᵀ * Rm * Am) by
      rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul],
      hμ, smul_smul, ← hm2, show m0⁻¹ * m0⁻¹ * m0 ^ 2 = 1 by field_simp, one_smul]
  set c' := m0⁻¹ * (m0⁻¹ * (c : K)) with hc'
  have hAA : Am * Am = (c : K) • 1 := by
    have e := congrArg Units.val hc
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar] at e
    rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hA2 : (m0⁻¹ • Am) * (m0⁻¹ • Am) = c' • 1 := by
    rw [show (m0⁻¹ • Am) * (m0⁻¹ • Am) = (m0⁻¹ * m0⁻¹) • (Am * Am) by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul], hAA, smul_smul, hc', mul_assoc]
  refine ⟨m0, hm00, hA'R, ?_⟩
  rw [hA2]
  have hRR : (c' • (1 : Matrix (Fin d) (Fin d) K))ᵀ * Rm * (c' • 1) = Rm := by
    rw [← hA2]
    calc ((m0⁻¹ • Am) * (m0⁻¹ • Am))ᵀ * Rm * ((m0⁻¹ • Am) * (m0⁻¹ • Am)) =
        (m0⁻¹ • Am)ᵀ * ((m0⁻¹ • Am)ᵀ * Rm * (m0⁻¹ • Am)) * (m0⁻¹ • Am) := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Rm := by rw [hA'R, hA'R]
  have hc'2 : c' * c' = 1 := by
    rw [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul] at hRR
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have hR0 : Rm ≠ 0 := fun h0 => hdR (by rw [h0, det_zero])
    have : (c' * c' - 1) • Rm = 0 := by rw [sub_smul, one_smul, hRR, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hR0)
  have hdetA' : (m0⁻¹ ^ d * Am.det) ^ 2 = 1 := by
    rw [mul_pow, hdet, ← hm2, ← pow_mul, ← pow_mul, mul_comm d 2, ← mul_pow,
      inv_mul_cancel₀ hm00, one_pow]
  have hcd : c' ^ d = 1 := by
    have e := congrArg Matrix.det hA2
    rw [det_mul, det_smul, det_smul, det_one, Fintype.card_fin, mul_one] at e
    rw [← e, ← pow_two]
    exact hdetA'
  have hc1 : c' = 1 := by
    have : c' ^ d = c' * (c' * c') ^ k := by
      rw [hk, pow_succ, ← pow_two, ← pow_mul]
      ring
    rw [hc'2, one_pow, mul_one] at this
    rw [← this, hcd]
  rw [hc1, one_smul]

end CFSG.ComponentClassification.Burgoyne.O
