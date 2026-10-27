module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev SoVec5 : Type := Fin 5 → ZMod 5

private instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[expose] noncomputable def soQuad5 : QuadraticForm (ZMod 5) SoVec5 :=
  (Matrix.toBilin' ((3 : ZMod 5) • soGram5)).toQuadraticMap

theorem soQuad5_apply (x : SoVec5) : soQuad5 x = x 0 * x 1 + x 2 * x 3 + x 4 * x 4 := by
  simp [soQuad5, Matrix.toBilin'_apply', soGram5, dotProduct, Fin.sum_univ_five, mulVec]
  have h5 : (5 : ZMod 5) = 0 := by decide
  linear_combination (x 0 * x 1 + x 2 * x 3 + x 4 * x 4) * h5

theorem eq_zero_of_polar_soQuad5 (x : SoVec5) (hx : ∀ y, QuadraticMap.polar soQuad5 x y = 0) :
    x = 0 := by
  have h : ∀ j : Fin 5, QuadraticMap.polar soQuad5 x (Pi.single j 1) = 0 := fun j => hx _
  simp only [QuadraticMap.polar, soQuad5_apply] at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp [Pi.single_apply] at h0 h1 h2 h3 h4
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e0 : x 0 = 0 := by linear_combination h1
  have e1 : x 1 = 0 := by linear_combination h0
  have e2 : x 2 = 0 := by linear_combination h3
  have e3 : x 3 = 0 := by linear_combination h2
  have e4 : x 4 = 0 := by linear_combination 3 * h4 - x 4 * h5
  funext i
  fin_cases i <;> assumption

theorem soQuad5_nondegenerate : (QuadraticMap.polarBilin soQuad5).Nondegenerate :=
  ⟨fun x hx => eq_zero_of_polar_soQuad5 x hx, fun y hy =>
    eq_zero_of_polar_soQuad5 y fun x => by rw [QuadraticMap.polar_comm]; exact hy x⟩

theorem soQuad5_eq_dot (x : SoVec5) : soQuad5 x = 3 * (x ⬝ᵥ soGram5 *ᵥ x) := by
  simp [soQuad5, Matrix.toBilin'_apply', Matrix.smul_mulVec, dotProduct_smul]

theorem natCard_orthogonalGroup_soQuad5 :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup soQuad5) = 18720000 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod 5) (n := 2)
    (by rw [ZMod.ringChar_zmod_n]; decide) soQuad5_nondegenerate (by simp)
  rw [Nat.card_zmod] at h
  have hp : (∏ i ∈ Finset.Icc 1 2, ((((5 : ℕ) : ℤ) ^ 2) ^ i - 1)) = 24 * 624 := by
    simp [Finset.prod_Icc_succ_top]
  rw [hp] at h
  exact_mod_cast h

@[expose] noncomputable def soGLEquiv : GL (Fin 5) (ZMod 5) ≃* (SoVec5 ≃ₗ[ZMod 5] SoVec5) :=
  (Matrix.GeneralLinearGroup.toLin).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem soGLEquiv_apply (M : GL (Fin 5) (ZMod 5)) (v : SoVec5) :
    soGLEquiv M v = (M : SoMat5) *ᵥ v := rfl

theorem dotProduct_mulVec_soGram5_of_isometry {M : SoMat5} (hM : Mᵀ * soGram5 * M = soGram5) (v : SoVec5) :
    (M *ᵥ v) ⬝ᵥ soGram5 *ᵥ (M *ᵥ v) = v ⬝ᵥ soGram5 *ᵥ v := by
  conv_rhs => rw [← hM]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem soGLEquiv_mem_orthogonalGroup {M : GL (Fin 5) (ZMod 5)}
    (hM : (M : SoMat5)ᵀ * soGram5 * (M : SoMat5) = soGram5) :
    soGLEquiv M ∈ TauCeti.QuadraticMap.orthogonalGroup soQuad5 := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [soGLEquiv_apply, soQuad5_eq_dot, soQuad5_eq_dot, dotProduct_mulVec_soGram5_of_isometry hM]

theorem card_soGroup5_le : Nat.card soGroup5 ≤ 9360000 := by
  let f : soGroup5 ⊕ soGroup5 → TauCeti.QuadraticMap.orthogonalGroup soQuad5 := fun
    | .inl M => ⟨soGLEquiv M, soGLEquiv_mem_orthogonalGroup M.2.1⟩
    | .inr M => ⟨soGLEquiv (-(M : GL (Fin 5) (ZMod 5))), soGLEquiv_mem_orthogonalGroup (by
        simp only [Units.val_neg, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
        exact M.2.1)⟩
  have hf : Function.Injective f := by
    have hdet : ∀ M N : soGroup5, (M : GL (Fin 5) (ZMod 5)) ≠ -(N : GL (Fin 5) (ZMod 5)) := by
      intro M N h
      have h1 := congrArg (fun A : GL (Fin 5) (ZMod 5) => (A : SoMat5).det) h
      simp only [Units.val_neg, Matrix.det_neg, M.2.2, N.2.2, Fintype.card_fin] at h1
      revert h1; decide
    rintro (M | M) (N | N) h <;> simp only [f, Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact absurd h (hdet M N)
    · exact absurd h.symm (hdet N M)
    · exact congrArg Sum.inr (Subtype.ext (neg_inj.mp h))
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup soQuad5) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_orthogonalGroup_soQuad5]; norm_num)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum, natCard_orthogonalGroup_soQuad5] at this
  omega

end CFSG.EvenSporadicStandard.TwoHS.GH312
