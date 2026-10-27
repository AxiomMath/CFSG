module

public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeIso
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207.D4Graph

open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Steinberg.Minuscule
  CFSG.TauCetiBridge.Twisted CFSG.TauCetiBridge.Minuscule
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped Matrix

theorem simple_root_exists : ∀ i : Fin Tag.D4.rank,
    (∃ k : Fin 24, Tag.D4.rootCertificate.root k = Pi.single i 1) ∧
      ∃ k : Fin 24, Tag.D4.rootCertificate.root k = -Pi.single i 1 := by
  decide +kernel

section Field

variable {K : Type} [Field K]


theorem sigmaOmega_symm_blockRepE_xm (σ : K ≃+* K) (k : Fin 24) (c : K) :
    sigmaOmega σ ((omegaEquiv K).symm
      (blockRepE K (d4tData_valid.xm K (Tag.D4.rootCertificate.root k) c))) =
      (omegaEquiv K).symm
        (blockRepE K (d4tData_valid.xm K (Tag.D4.rootCertificate.root k) (σ c))) := by
  apply (omegaEquiv K).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨y, rfl⟩ : ∃ y : V K, (fun i => σ (y i)) = v :=
    ⟨fun i => σ.symm (v i), by funext i; simp⟩
  rw [omegaEquiv_sigmaOmega_apply, MulEquiv.apply_symm_apply, coe_blockRepE, coe_blockRepE,
    blockRep_xm, blockRep_xm]
  have hne := (rootData_spec k).1
  have hpol : polar (quadPlus 4 K) (Pi.single (rU k) 1)
      ((((rS k : ℤ) : K) * c) • Pi.single (rW k) 1) = 0 := by
    rw [polar_smul_right, polar_single_single hne, smul_zero]
  rw [sigma_eichler σ (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.quadPlus_single
    (F := K) (rU k)) hpol y]
  have h1 : (fun i => σ ((Pi.single (rU k) 1 : V K) i)) = Pi.single (rU k) 1 := by
    funext j
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h2 : (fun i => σ (((((rS k : ℤ) : K) * c) • (Pi.single (rW k) 1 : V K)) i)) =
      (((rS k : ℤ) : K) * σ c) • Pi.single (rW k) 1 := by
    funext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [h1, h2]

end Field

section Equivariance

variable {K : Type} [Field K]


theorem thetaOmega_sigmaOmega_xm_single (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    thetaOmega K (sigmaOmega σ ((omegaEquiv K).symm
      (blockRepE K (d4tData_valid.xm K (Pi.single i 1) c)))) =
      entrywiseAdjointAut Tag.D4 σ (adjRep K (d4tData_valid.xm K (Pi.single i 1) c)) := by
  obtain ⟨k, hk⟩ := (simple_root_exists i).1
  have h1 : thetaOmega K (sigmaOmega σ ((omegaEquiv K).symm
      (blockRepE K (d4tData_valid.xm K (Pi.single i 1) c)))) =
      adjRep K (d4tData_valid.xm K (Pi.single i 1) (σ c)) := by
    rw [← hk, sigmaOmega_symm_blockRepE_xm]
    change theta K ((omegaEquiv K) ((omegaEquiv K).symm _)) = _
    rw [MulEquiv.apply_symm_apply, theta_blockRepE]
  have hx : ∀ t : K, adjRep K (d4tData_valid.xm K (Pi.single i 1) t) = adjX Tag.D4 K i t :=
    fun t => Subtype.ext (adMin_xm_single (hV := d4tData_valid) (hpd := posDef_cartan_D4)
      (hS := d4tSigns_check) (K := K) i t)
  rw [h1, hx, hx]
  exact (Subtype.ext (units_map_entrywiseHom_xUnit σ.toRingHom i c)).symm

theorem thetaOmega_sigmaOmega_xm_neg_single (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    thetaOmega K (sigmaOmega σ ((omegaEquiv K).symm
      (blockRepE K (d4tData_valid.xm K (-Pi.single i 1) c)))) =
      entrywiseAdjointAut Tag.D4 σ (adjRep K (d4tData_valid.xm K (-Pi.single i 1) c)) := by
  obtain ⟨k, hk⟩ := (simple_root_exists i).2
  have h1 : thetaOmega K (sigmaOmega σ ((omegaEquiv K).symm
      (blockRepE K (d4tData_valid.xm K (-Pi.single i 1) c)))) =
      adjRep K (d4tData_valid.xm K (-Pi.single i 1) (σ c)) := by
    rw [← hk, sigmaOmega_symm_blockRepE_xm]
    change theta K ((omegaEquiv K) ((omegaEquiv K).symm _)) = _
    rw [MulEquiv.apply_symm_apply, theta_blockRepE]
  have hx : ∀ t : K, adjRep K (d4tData_valid.xm K (-Pi.single i 1) t) = adjY Tag.D4 K i t :=
    fun t => Subtype.ext (adMin_xm_neg_single (hV := d4tData_valid) (hpd := posDef_cartan_D4)
      (hS := d4tSigns_check) (K := K) i t)
  rw [h1, hx, hx]
  exact (Subtype.ext (units_map_entrywiseHom_yUnit σ.toRingHom i c)).symm

theorem thetaOmega_sigmaOmega (σ : K ≃+* K) (A : StatedOmega (StatedQuadPlus 4 K)) :
    thetaOmega K (sigmaOmega σ A) = entrywiseAdjointAut Tag.D4 σ (thetaOmega K A) := by
  have key : (thetaOmega K).comp ((sigmaOmega σ).toMonoidHom.comp
        ((omegaEquiv K).symm.toMonoidHom.comp (blockRepE K))) =
      (entrywiseAdjointAut Tag.D4 σ).toMonoidHom.comp (adjRep K) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top d4tData_valid K) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact thetaOmega_sigmaOmega_xm_single σ i c
    · exact thetaOmega_sigmaOmega_xm_neg_single σ i c
  obtain ⟨g, hg⟩ := blockRepE_surjective K (omegaEquiv K A)
  have hA : A = (omegaEquiv K).symm (blockRepE K g) := by rw [hg, MulEquiv.symm_apply_apply]
  have h := DFunLike.congr_fun key g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [hA]
  change _ = entrywiseAdjointAut Tag.D4 σ (theta K ((omegaEquiv K) ((omegaEquiv K).symm _)))
  rw [MulEquiv.apply_symm_apply, theta_blockRepE]
  exact h

end Equivariance

section Image

variable {K : Type} [Field K]

theorem reindexQuadPlus_map (σ : K ≃+* K) (v : Fin (2 * 4) → K) :
    reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K) (fun i => σ (v i)) =
      σ (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K) v) := by
  rw [reindexQuadraticForm_apply, reindexQuadraticForm_apply]
  exact quadPlus_map σ _

theorem inr_mem_similarityPairs_reindex (σ : K ≃+* K) :
    (SemidirectProduct.inr σ : coordinateSemilinearGroup (2 * 4) K) ∈
      similarityPairs (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K)) := by
  refine ⟨1, fun v => ?_⟩
  have hv : coordinateSemilinearMap (SemidirectProduct.inr σ : coordinateSemilinearGroup (2 * 4) K)
      v = fun i => σ (v i) := by
    rw [coordinateSemilinearMap_apply]
    simp
  rw [hv, reindexQuadPlus_map]
  simp

theorem matrixDerivedConjugation_inr_reindex (σ : K ≃+* K)
    (x : StatedOmega (StatedQuadPlus 4 K)) :
    matrixDerivedConjugation (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K))
        ⟨SemidirectProduct.inr σ, inr_mem_similarityPairs_reindex σ⟩
        (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) x) =
      statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
        (sigmaOmega σ x) := by
  apply Subtype.ext
  rw [matrixDerivedConjugation_val]
  apply Units.ext
  ext i j
  simp only [SemidirectProduct.left_inr, SemidirectProduct.right_inr, one_mul, inv_one, mul_one]
  change σ (((statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K)
    (coe_quadPlus 4 K) x).val : Matrix.GeneralLinearGroup (Fin (2 * 4)) K).val i j) = _
  rw [statedDerivedReindexEquiv_entry, statedDerivedReindexEquiv_entry, val_sigmaOmega]
  rfl

end Image

section Member

variable {K : Type} [Field K] [Finite K]


theorem coordinatePlusWitnessEquiv_isoAdj_symm_thetaOmega
    (x : StatedOmega (StatedQuadPlus 4 K)) :
    coordinatePlusWitnessEquiv K (isoAdj K).symm (thetaOmega K x) =
      matrixProjectiveProjection (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K))
        (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) x) := by
  have h : (isoAdj K).symm (thetaOmega K x) = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    exact (isoAdj_mk K x).symm
  change statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)
    ((isoAdj K).symm (thetaOmega K x)) = _
  rw [h]
  exact statedProjectiveReindexEquiv_mk (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) x

theorem congr_entrywiseAdjointAut_eq (σ : K ≃+* K) :
    MulAut.congr (coordinatePlusWitnessEquiv K (isoAdj K).symm) (entrywiseAdjointAut Tag.D4 σ) =
      matrixProjectiveConjugation (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K))
        ⟨SemidirectProduct.inr σ, inr_mem_similarityPairs_reindex σ⟩ := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨c, rfl⟩ := (coordinatePlusWitnessEquiv K (isoAdj K).symm).surjective y
  obtain ⟨x, rfl⟩ := thetaOmega_surjective K c
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [← thetaOmega_sigmaOmega σ x, coordinatePlusWitnessEquiv_isoAdj_symm_thetaOmega,
    coordinatePlusWitnessEquiv_isoAdj_symm_thetaOmega]
  have hconj := matrixProjectiveConjugation_mk
    (reindexQuadraticForm (plusIndexEquiv 4) (quadPlus 4 K))
    ⟨SemidirectProduct.inr σ, inr_mem_similarityPairs_reindex σ⟩
    (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) x)
  exact (congrArg (matrixProjectiveProjection (reindexQuadraticForm (plusIndexEquiv 4)
    (quadPlus 4 K))) (matrixDerivedConjugation_inr_reindex σ x)).symm.trans hconj.symm

theorem congr_entrywiseAdjointAut_mem (σ : K ≃+* K) :
    MulAut.congr (coordinatePlusWitnessEquiv K (isoAdj K).symm) (entrywiseAdjointAut Tag.D4 σ) ∈
      matrixProjectiveImage (coordinateQuadPlus 4 K) :=
  ⟨⟨SemidirectProduct.inr σ, inr_mem_similarityPairs_reindex σ⟩,
    (congr_entrywiseAdjointAut_eq σ).symm⟩

end Member

end CFSG.HardMathSupport.Dickson.Bal207.D4Graph

end
