module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBODiag
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexVectorEquiv
  reindexQuadraticForm reindexMatrixEquiv reindexMatrixEquiv_val reindexVectorEquiv_apply
  reindexVectorEquiv_symm_apply reindexQuadraticForm_map)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)
open scoped MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

theorem mulVec_inv_mulVec (S : GL (Fin d) K) (y : Fin d → K) :
    (S : Matrix (Fin d) (Fin d) K) *ᵥ (((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ y) =
      y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable {σ : Type} [Fintype σ] [DecidableEq σ]

@[expose] def tTrans (e : σ ≃ Fin d) (S₁ S₂ : GL (Fin d) K) : (σ → K) ≃ₗ[K] (Fin d → K) :=
  (reindexVectorEquiv e).trans ((matrixLinearEquiv S₁).trans (matrixLinearEquiv S₂))

omit [Fintype σ] [DecidableEq σ] in
theorem tTrans_apply (e : σ ≃ Fin d) (S₁ S₂ : GL (Fin d) K) (v : σ → K) :
    tTrans e S₁ S₂ v = (S₂ : Matrix (Fin d) (Fin d) K) *ᵥ ((S₁ : Matrix (Fin d) (Fin d) K) *ᵥ
      reindexVectorEquiv e v) := rfl

omit [DecidableEq σ] in
theorem reindex_mulVec (e : σ ≃ Fin d) (M : Matrix σ σ K) (u : Fin d → K) :
    Matrix.reindex e e M *ᵥ u = reindexVectorEquiv e (M *ᵥ (reindexVectorEquiv e).symm u) := by
  funext i
  rw [reindex_apply, submatrix_mulVec_equiv, reindexVectorEquiv_apply]
  rfl

omit [DecidableEq σ] in
theorem conj_eq_of_mulVec (e : σ ≃ Fin d) (S₁ S₂ : GL (Fin d) K) {M : Matrix σ σ K}
    {N : Matrix (Fin d) (Fin d) K}
    (h : ∀ z, M *ᵥ z = (tTrans e S₁ S₂).symm (N *ᵥ tTrans e S₁ S₂ z)) :
    (S₂ : Matrix (Fin d) (Fin d) K) * ((S₁ : Matrix (Fin d) (Fin d) K) * Matrix.reindex e e M *
      ((S₁⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
        ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = N := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  simp only [← Matrix.mulVec_mulVec]
  rw [reindex_mulVec]
  set z := (reindexVectorEquiv e).symm (((S₁⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
    (((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v)) with hz
  have hTz : tTrans e S₁ S₂ z = v := by
    rw [tTrans_apply, hz, LinearEquiv.apply_symm_apply, mulVec_inv_mulVec, mulVec_inv_mulVec]
  rw [h z, hTz, ← tTrans_apply, LinearEquiv.apply_symm_apply]

theorem theta_mk (e : σ ≃ Fin d) (Q₀ : QuadraticForm K (σ → K)) {Q0 : (σ → K) → K}
    (hQ : ⇑Q₀ = Q0) {Q₁ Q₂ : QuadraticForm K (Fin d → K)} (S₁ : GL (Fin d) K) (ν₁ : Kˣ)
    (hS₁ : ∀ v, Q₁ ((S₁ : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν₁ * reindexQuadraticForm e Q₀ v)
    (S₂ : GL (Fin d) K) (ν₂ : Kˣ)
    (hS₂ : ∀ v, Q₂ ((S₂ : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν₂ * Q₁ v) (A : StatedOmega Q0) :
    ∃ X : matrixDerived Q₂, ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (S₂ : Matrix (Fin d) (Fin d) K) * ((S₁ : Matrix (Fin d) (Fin d) K) *
          Matrix.reindex e e ((A : GL σ K) : Matrix σ σ K) *
          ((S₁⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
          ((S₂⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ∧
      ((statedProjectiveReindexEquiv e Q₀ hQ).trans
        ((oTransport S₁ ν₁ hS₁).trans (oTransport S₂ ν₂ hS₂))) (QuotientGroup.mk' _ A) =
        projH _ X := by
  refine ⟨derivedTransport S₂ ν₂ hS₂ (derivedTransport S₁ ν₁ hS₁
    (statedDerivedReindexEquiv e Q₀ hQ A)), ?_, ?_⟩
  · rw [coe_derivedTransport, coe_derivedTransport, statedDerivedReindexEquiv_val]
    simp only [Units.val_mul, reindexMatrixEquiv_val]
  · change oTransport S₂ ν₂ hS₂ (oTransport S₁ ν₁ hS₁
      (statedProjectiveReindexEquiv e Q₀ hQ (QuotientGroup.mk' _ A))) = _
    rw [statedProjectiveReindexEquiv_mk]
    change oTransport S₂ ν₂ hS₂ (oTransport S₁ ν₁ hS₁ (projH _ _)) = _
    rw [oTransport_proj, oTransport_proj]

variable [Finite K]

theorem spin_slices_bridge (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd5 : 5 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW (by omega : 4 ≤ d) w α a)
    (e : σ ≃ Fin d) (Q₀ : QuadraticForm K (σ → K)) {Q0 : (σ → K) → K} (hQ : ⇑Q₀ = Q0)
    (hR : (spinMatrix Q₀).range = StatedOmega Q0) {Q₁ : QuadraticForm K (Fin d → K)}
    (S₁ : GL (Fin d) K) (ν₁ : Kˣ)
    (hS₁ : ∀ v, Q₁ ((S₁ : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν₁ * reindexQuadraticForm e Q₀ v)
    (S₂ : GL (Fin d) K) (ν₂ : Kˣ)
    (hS₂ : ∀ v, oQ (diagGL hw) ((S₂ : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν₂ * Q₁ v) :
    ∃ R₁ R₂ : SL(2, K) →* spinGroup Q₀,
      ((R₁ (-1) * R₂ (-1) : spinGroup Q₀) : CliffordAlgebra Q₀) = -1 ∧
      (∀ g, ∃ g', ((statedProjectiveReindexEquiv e Q₀ hQ).trans
        ((oTransport S₁ ν₁ hS₁).trans (oTransport S₂ ν₂ hS₂))) (spinToStatedProj Q₀ hR (R₁ g)) =
          projH _ (oSliceH h2 hK4 (by omega) hw hW g')) ∧
      (∀ g, ∃ g', ((statedProjectiveReindexEquiv e Q₀ hQ).trans
        ((oTransport S₁ ν₁ hS₁).trans (oTransport S₂ ν₂ hS₂))) (spinToStatedProj Q₀ hR (R₂ g)) =
          projH _ (oSliceRH h2 hK4 (by omega) hw hW g')) := by
  have hd4 : 4 ≤ d := by omega
  set T := tTrans e S₁ S₂ with hTdef
  have hT : ∀ v, oQ (diagGL hw) (T v) = ((ν₂ * ν₁ : Kˣ) : K) * Q₀ v := by
    intro v
    rw [tTrans_apply, hS₂, hS₁, reindexQuadraticForm_map, Units.val_mul, mul_assoc]
  set Fr₀ := frameComap (diagFrame hw h2 hW) hT with hFr₀
  set a₀ := T.symm (Pi.single ⟨4, by omega⟩ 1) with ha₀
  obtain ⟨hu, hp1, hp2, hp3, hp4⟩ := diagFrame_perp hw h2 hd5 hW
  have ha₀u : IsUnit (Q₀ a₀) := by
    rw [ha₀, Q_symm hT]
    exact (Units.isUnit _).mul hu
  have hperp : polar Q₀ Fr₀.e₁ a₀ = 0 ∧ polar Q₀ Fr₀.f₁ a₀ = 0 ∧ polar Q₀ Fr₀.e₂ a₀ = 0 ∧
      polar Q₀ Fr₀.f₂ a₀ = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hFr₀, frameComap_e₁, ha₀, polar_symm hT, hp1, mul_zero]
    · rw [hFr₀, frameComap_f₁, ha₀, polar_smul_left, polar_symm hT, hp2, mul_zero, smul_zero]
    · rw [hFr₀, frameComap_e₂, ha₀, polar_symm hT, hp3, mul_zero]
    · rw [hFr₀, frameComap_f₂, ha₀, polar_smul_left, polar_symm hT, hp4, mul_zero, smul_zero]
  set H := frameHyp Fr₀ a₀ ha₀u hperp with hH
  refine ⟨H.longSL2 (show (0 : Fin 2) ≠ 1 by decide) true true,
    H.longSL2 (show (0 : Fin 2) ≠ 1 by decide) true false,
    frameHyp_longSL2_neg_one_mul Fr₀ a₀ ha₀u hperp, fun g => ?_, fun g => ?_⟩
  · refine ⟨conjSL₂ (dGL (Units.mk0 α hW.hα))⁻¹ (conjSL₂ (dGL (ν₂ * ν₁)) g), ?_⟩
    obtain ⟨X, hX, hΘ⟩ := theta_mk e Q₀ hQ S₁ ν₁ hS₁ S₂ ν₂ hS₂
      ⟨spinMatrix Q₀ (H.longSL2 (show (0 : Fin 2) ≠ 1 by decide) true true g),
        spinMatrix_mem_of_range_eq Q₀ hR _⟩
    rw [spinToStatedProj_apply]
    refine hΘ.trans (congrArg _ (Subtype.ext (Units.ext ?_)))
    rw [hX, coe_oSliceH]
    refine conj_eq_of_mulVec e S₁ S₂ fun z => ?_
    rw [spinMatrix_mulVec, spinAction_frameHyp_longSL2, frameComap_La, diagFrame_La]
  · refine ⟨(sigmaSL g)⁻¹, ?_⟩
    obtain ⟨X, hX, hΘ⟩ := theta_mk e Q₀ hQ S₁ ν₁ hS₁ S₂ ν₂ hS₂
      ⟨spinMatrix Q₀ (H.longSL2 (show (0 : Fin 2) ≠ 1 by decide) true false g),
        spinMatrix_mem_of_range_eq Q₀ hR _⟩
    rw [spinToStatedProj_apply]
    refine hΘ.trans (congrArg _ (Subtype.ext (Units.ext ?_)))
    rw [hX, coe_oSliceRH]
    refine conj_eq_of_mulVec e S₁ S₂ fun z => ?_
    rw [spinMatrix_mulVec, spinAction_frameHyp_longSL2_swap, frameComap_swap_La,
      diagFrame_swap_La]

end CFSG.ComponentClassification.Burgoyne.B
