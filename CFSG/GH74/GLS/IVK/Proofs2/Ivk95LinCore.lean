module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionNonsquareComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitMatrix
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped MatrixGroups Matrix

section Core

variable {k : Type} [Field k] [Finite k] {m : ℕ}

omit [Finite k] in
theorem ivk95l_operator_nonscalar (hm : 0 < m) {T : GL (Fin m) k}
    (hns : ∀ c : kˣ, T ≠ Matrix.GeneralLinearGroup.scalar (Fin m) c) :
    ∀ c : k, splitMatrixOperator T ≠ c • (1 : Module.End k (Fin m → k)) := by
  intro c hc
  have hmul : ∀ v : Fin m → k, (T : Matrix (Fin m) (Fin m) k) *ᵥ v = c • v := fun v => by
    have h1 := LinearMap.congr_fun hc v
    have h2 : splitMatrixOperator T v = (T : Matrix (Fin m) (Fin m) k) *ᵥ v := rfl
    rw [h2] at h1
    simpa using h1
  have hT : (T : Matrix (Fin m) (Fin m) k) = c • (1 : Matrix (Fin m) (Fin m) k) := by
    ext i j
    have := congrFun (hmul (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : (T : Matrix (Fin m) (Fin m) k) * ((T⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hT, h0, zero_smul, zero_mul] at h1
    have := congrFun (congrFun h1 ⟨0, hm⟩) ⟨0, hm⟩
    simp at this
  refine hns (Units.mk0 c hc0) (Units.ext ?_)
  rw [hT, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

omit [Finite k] in
theorem ivk95l_split (htwo : (2 : k) ≠ 0) (hm : 0 < m) {T : GL (Fin m) k} {c₀ : kˣ}
    (hsq : T ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin m) (c₀ ^ 2))
    (hns : ∀ c : kˣ, T ≠ Matrix.GeneralLinearGroup.scalar (Fin m) c) :
    ∃ a b : ℕ, a + b = m ∧ 1 ≤ a ∧ 1 ≤ b ∧
      ∃ Θ : Subgroup.centralizer ({T} : Set (GL (Fin m) k)) ≃* GL (Fin a) k × GL (Fin b) k,
        ∀ (c : kˣ) (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
            Subgroup.centralizer ({T} : Set (GL (Fin m) k))),
          Θ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩ =
            (Matrix.GeneralLinearGroup.scalar (Fin a) c, Matrix.GeneralLinearGroup.scalar (Fin b) c) := by
  have hsum := splitMatrixDimension_sum T c₀ htwo hsq
  obtain ⟨hpos, hneg⟩ := splitMatrixDimension_pos T c₀ htwo hsq (ivk95l_operator_nonscalar hm hns)
  refine ⟨positiveMatrixDimension T c₀.val, negativeMatrixDimension T c₀.val, ?_, hpos, hneg,
    matrixCentralizerSplitEquiv T c₀ htwo hsq, fun c hc => ?_⟩
  · rw [hsum, Fintype.card_fin]
  · exact matrixCentralizerSplitEquiv_scalar T c₀ htwo hsq c

theorem ivk95l_quad {T : GL (Fin m) k} {μ : kˣ} (hμ : ¬ IsSquare μ.val)
    (hsq : T ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin m) μ) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : Algebra k E) (d : ℕ), m = 2 * d ∧
      Nat.card E = Nat.card k ^ 2 ∧
      ∃ Θ : Subgroup.centralizer ({T} : Set (GL (Fin m) k)) ≃* GL (Fin d) E,
        ∀ (c : kˣ) (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈
            Subgroup.centralizer ({T} : Set (GL (Fin m) k))),
          Θ ⟨Matrix.GeneralLinearGroup.scalar (Fin m) c, hc⟩ =
            Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (algebraMap k E).toMonoidHom c) := by
  have : Fact (¬ IsSquare μ.val) := ⟨hμ⟩
  have : Finite (extension μ.val) := quadraticExtension_finite μ.val
  refine ⟨extension μ.val, inferInstance, this, inferInstance, matrixDimension T μ hsq, ?_, ?_,
    matrixCentralizerQuadraticEquiv T μ hsq, fun c hc => ?_⟩
  · have := matrixDimension_twice T μ hsq
    rw [Fintype.card_fin] at this
    exact this
  · let _ := matrixModule T μ hsq
    let : Fintype k := Fintype.ofFinite k
    let : Fintype (extension μ.val) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
      extension_finrank]
  · exact matrixCentralizerQuadraticEquiv_scalar T μ hsq c

end Core

end CFSG.GH74.GLS.IVK.Proofs2
