module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8h
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8a

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit (extension)

variable {K : Type} [Field K] {b c : K}

theorem conj_eq_mul_scalar (hQ0 : ∃ v, Q8 K b c v ≠ 0) (ψ : MulAut (G0 K b c))
    (g : similarityPairs (Q8 K b c))
    (hg : matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ)
    (w : orthogonalDerived (Q8 K b c))
    (hw : ψ ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) w)) =
      (theta K b c hQ0).symm (QuotientGroup.mk' _ w)) :
    ∃ a : Kˣ, (matrixDerivedConjugation (Q8 K b c) g ((derivedEquiv (Q8 K b c)).symm w)).val =
      ((derivedEquiv (Q8 K b c)).symm w).val * GeneralLinearGroup.scalar (Fin (2 * 4)) a := by
  have hpx : psiC K b c ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) w)) =
      matrixProjectiveProjection (Q8 K b c) ((derivedEquiv (Q8 K b c)).symm w) := by
    rw [MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply, projectiveEquiv_symm_mk]
  have hcg : ∀ z, MulAut.congr (psiC K b c) ψ (psiC K b c z) = psiC K b c (ψ z) := fun z => by
    rw [MulAut.congr_apply]
    simp
  have h1 : matrixProjectiveConjugation (Q8 K b c) g
      (psiC K b c ((theta K b c hQ0).symm (QuotientGroup.mk' _ w))) =
      psiC K b c ((theta K b c hQ0).symm (QuotientGroup.mk' _ w)) := by
    change matrixProjectiveConjugationHom (Q8 K b c) g _ = _
    rw [hg, hcg, hw]
  rw [hpx, matrixProjectiveConjugation_mk] at h1
  have h2 := QuotientGroup.eq.mp h1
  obtain ⟨a, ha⟩ := (mem_matrixDerivedScalars_iff (Q8 K b c) _).mp h2
  refine ⟨a⁻¹, ?_⟩
  have h3 : ((derivedEquiv (Q8 K b c)).symm w).val =
      (matrixDerivedConjugation (Q8 K b c) g ((derivedEquiv (Q8 K b c)).symm w)).val *
        GeneralLinearGroup.scalar (Fin (2 * 4)) a := by
    rw [ha]
    simp
  have h4 : GeneralLinearGroup.scalar (Fin (2 * 4)) a *
      GeneralLinearGroup.scalar (Fin (2 * 4)) a⁻¹ = 1 := by
    rw [← map_mul (GeneralLinearGroup.scalar (Fin (2 * 4))) a a⁻¹, mul_inv_cancel, map_one]
  calc (matrixDerivedConjugation (Q8 K b c) g ((derivedEquiv (Q8 K b c)).symm w)).val
      = (matrixDerivedConjugation (Q8 K b c) g ((derivedEquiv (Q8 K b c)).symm w)).val *
          (GeneralLinearGroup.scalar (Fin (2 * 4)) a *
            GeneralLinearGroup.scalar (Fin (2 * 4)) a⁻¹) := by rw [h4, mul_one]
    _ = _ := by rw [← mul_assoc, ← h3]

theorem conj_eq_of_pow [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hQ0 : ∃ v, Q8 K b c v ≠ 0) (ψ : MulAut (G0 K b c)) (g : similarityPairs (Q8 K b c))
    (hg : matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ)
    (w : orthogonalDerived (Q8 K b c)) (hwp : w ^ p = 1)
    (hw : ψ ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) w)) =
      (theta K b c hQ0).symm (QuotientGroup.mk' _ w)) :
    matrixDerivedConjugation (Q8 K b c) g ((derivedEquiv (Q8 K b c)).symm w) =
      (derivedEquiv (Q8 K b c)).symm w := by
  obtain ⟨a, ha⟩ := conj_eq_mul_scalar hQ0 ψ g hg w hw
  have hY : ((derivedEquiv (Q8 K b c)).symm w) ^ p = 1 := by rw [← map_pow, hwp, map_one]
  apply Subtype.ext
  refine eq_of_eq_mul_scalar (by norm_num) a ?_ ?_ ha
  · rw [← Subgroup.coe_pow, ← map_pow, hY, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, hY, Subgroup.coe_one]

theorem toLin'_derived (w : orthogonalDerived (Q8 K b c)) :
    Matrix.toLin' ((derivedEquiv (Q8 K b c)).symm w).val.val = w.val.val.toLinearMap := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, derivedEquiv_symm_val]
  change matrixLinearIso (matrixLinearIso.symm w.val.val) v = w.val.val v
  rw [MulEquiv.apply_symm_apply]

theorem trace_derived (c₀ : K) [Fact (¬ IsSquare c₀)]
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀)) (U : Matrix (Fin 4) (Fin 4) (extension c₀))
    (w : orthogonalDerived (Q8 K b c)) (hw : ∀ v, w.val.val v = χ.symm (U *ᵥ χ v)) :
    ((derivedEquiv (Q8 K b c)).symm w).val.val.trace = 2 * U.trace.re := by
  rw [← Matrix.trace_toLin'_eq, toLin'_derived]
  have h : w.val.val.toLinearMap = χ.symm.conj ((Matrix.mulVecLin U).restrictScalars K) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.coe_toLinearMap, hw, LinearEquiv.conj_apply_apply]
    rfl
  rw [h, LinearMap.trace_conj', trace_restrictScalars]

theorem trace_A_derived (c₀ : K) [Fact (¬ IsSquare c₀)]
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀)) (U : Matrix (Fin 4) (Fin 4) (extension c₀))
    (A : GL (Fin (2 * 4)) K)
    (hA : ∀ v, χ (A.val *ᵥ v) = (QuadraticAlgebra.omega : extension c₀) • χ v)
    (w : orthogonalDerived (Q8 K b c)) (hw : ∀ v, w.val.val v = χ.symm (U *ᵥ χ v)) :
    (A.val * ((derivedEquiv (Q8 K b c)).symm w).val.val).trace = 2 * (c₀ * U.trace.im) := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_mul, toLin'_derived]
  have h : Matrix.toLin' A.val ∘ₗ w.val.val.toLinearMap = χ.symm.conj
      ((Matrix.mulVecLin ((QuadraticAlgebra.omega : extension c₀) • U)).restrictScalars K) := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hw, Matrix.toLin'_apply,
      LinearEquiv.conj_apply_apply]
    apply χ.injective
    rw [hA, LinearEquiv.apply_symm_apply]
    change _ = χ (χ.symm (((QuadraticAlgebra.omega : extension c₀) • U) *ᵥ χ v))
    rw [LinearEquiv.apply_symm_apply, Matrix.smul_mulVec]
  rw [h, LinearMap.trace_conj', trace_restrictScalars_omega]

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
