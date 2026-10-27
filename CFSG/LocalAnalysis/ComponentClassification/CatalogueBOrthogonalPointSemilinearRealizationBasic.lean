module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointKernelBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization

open Matrix CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalPointKernel

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def detwist (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  { (coordinateFieldMap d sigma.symm).trans T.toAddEquiv with
    map_smul' a v := by
      change T (coordinateFieldMap d sigma.symm (a • v)) =
        a • T (coordinateFieldMap d sigma.symm v)
      rw [coordinateFieldMap_smul, T.map_smulₛₗ]
      change sigma (sigma.symm a) • T (coordinateFieldMap d sigma.symm v) = _
      rw [sigma.apply_symm_apply] }

theorem detwist_apply (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    detwist sigma T v = T (fun i => sigma.symm (v i)) := rfl

theorem detwist_symm_apply (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    (detwist sigma T).symm v = fun i => sigma (T.symm v i) := rfl

theorem detwist_twist (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    detwist sigma T (coordinateFieldMap d sigma v) = T v := by
  rw [detwist_apply]
  congr 1
  funext i
  exact sigma.symm_apply_apply (v i)

theorem semilinear_eq_detwist_twist (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    T v = detwist sigma T (coordinateFieldMap d sigma v) :=
  (detwist_twist sigma T v).symm

theorem semilinear_symm_eq_detwist_symm (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    T.symm v = coordinateFieldMap d sigma.symm ((detwist sigma T).symm v) := by
  rw [detwist_symm_apply]
  funext i
  exact (sigma.symm_apply_apply (T.symm v i)).symm

@[expose] def realizingMatrix (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) : GL (Fin d) K :=
  matrixLinearIso.symm (detwist sigma T)

theorem realizingMatrix_linearEquiv (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    matrixLinearEquiv (realizingMatrix sigma T) = detwist sigma T :=
  matrixLinearIso.apply_symm_apply (detwist sigma T)

theorem realizingMatrix_mulVec (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    (realizingMatrix sigma T).val *ᵥ v = T (fun i => sigma.symm (v i)) := by
  rw [← matrixLinearEquiv_apply, realizingMatrix_linearEquiv, detwist_apply]

theorem coordinateFieldMap_single_one (sigma : K ≃+* K) (j : Fin d) :
    coordinateFieldMap d sigma (Pi.single j (1 : K)) = Pi.single j 1 := by
  classical
  funext i
  by_cases h : i = j
  · subst i
    simp [coordinateFieldMap]
  · simp [coordinateFieldMap, h]

theorem realizingMatrix_entry (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (i j : Fin d) :
    (realizingMatrix sigma T).val i j = T (Pi.single j 1) i := by
  have h := congrArg (fun v : Fin d → K => v i)
    (realizingMatrix_mulVec sigma T (Pi.single j 1))
  rw [Matrix.mulVec_single_one] at h
  change _ = T (coordinateFieldMap d sigma.symm (Pi.single j 1)) i at h
  rw [coordinateFieldMap_single_one] at h
  exact h

theorem realizingMatrix_inverse_mulVec (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    (realizingMatrix sigma T)⁻¹.val *ᵥ v = fun i => sigma (T.symm v i) := by
  change matrixLinearEquiv ((realizingMatrix sigma T)⁻¹) v = _
  change matrixLinearIso ((realizingMatrix sigma T)⁻¹) v = _
  rw [map_inv]
  change (matrixLinearEquiv (realizingMatrix sigma T)).symm v = _
  rw [realizingMatrix_linearEquiv, detwist_symm_apply]

@[expose] def realizingPair (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    coordinateSemilinearGroup d K := SemidirectProduct.mk (realizingMatrix sigma T) sigma

theorem realizingPair_left (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    (realizingPair sigma T).left = realizingMatrix sigma T := rfl

theorem realizingPair_right (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    (realizingPair sigma T).right = sigma := rfl

theorem realizingPair_apply (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    coordinateSemilinearMap (realizingPair sigma T) v = T v := by
  change matrixLinearEquiv (realizingMatrix sigma T) (coordinateFieldMap d sigma v) = _
  rw [realizingMatrix_linearEquiv, detwist_twist]

theorem realizingPair_addEquiv (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    coordinateSemilinearMap (realizingPair sigma T) = T.toAddEquiv :=
  AddEquiv.ext (realizingPair_apply sigma T)

theorem realizingPair_inverse_apply (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (v : Fin d → K) :
    coordinateSemilinearMap (realizingPair sigma T)⁻¹ v = T.symm v := by
  rw [coordinateSemilinearMap_inv, realizingPair_addEquiv]
  rfl

theorem realizingPair_linearMap (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    coordinateSemilinearLinearMap (realizingPair sigma T) = T.toLinearMap :=
  LinearMap.ext (realizingPair_apply sigma T)

theorem realizingPair_semilinearEquiv (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    coordinateSemilinearEquiv (realizingPair sigma T) = T :=
  LinearEquiv.ext (realizingPair_apply sigma T)

theorem realizingMatrix_unique (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (A : GL (Fin d) K)
    (hA : ∀ v, coordinateSemilinearMap (SemidirectProduct.mk A sigma) v = T v) :
    A = realizingMatrix sigma T := by
  apply matrixLinearIso.injective
  change matrixLinearEquiv A = matrixLinearEquiv (realizingMatrix sigma T)
  rw [realizingMatrix_linearEquiv]
  apply LinearEquiv.ext
  intro v
  have h := hA (coordinateFieldMap d sigma.symm v)
  change matrixLinearEquiv A
    (coordinateFieldMap d sigma (coordinateFieldMap d sigma.symm v)) = _ at h
  have ht : coordinateFieldMap d sigma (coordinateFieldMap d sigma.symm v) = v := by
    funext i
    exact sigma.apply_symm_apply (v i)
  rw [ht] at h
  exact h

theorem existsUnique_realizingMatrix (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    ∃! A : GL (Fin d) K,
      ∀ v, coordinateSemilinearMap (SemidirectProduct.mk A sigma) v = T v := by
  refine ⟨realizingMatrix sigma T, realizingPair_apply sigma T, ?_⟩
  exact fun A hA => realizingMatrix_unique sigma T A hA

theorem realizingPair_unique (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K))
    (g : coordinateSemilinearGroup d K) (hsigma : g.right = sigma)
    (hT : ∀ v, coordinateSemilinearMap g v = T v) : g = realizingPair sigma T := by
  have hg : g = SemidirectProduct.mk g.left sigma :=
    SemidirectProduct.ext rfl hsigma
  have hA := realizingMatrix_unique sigma T g.left (by simpa only [← hg] using hT)
  exact SemidirectProduct.ext hA hsigma

theorem existsUnique_realizingPair (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) :
    ∃! g : coordinateSemilinearGroup d K,
      g.right = sigma ∧ coordinateSemilinearMap g = T.toAddEquiv := by
  refine ⟨realizingPair sigma T, ⟨rfl, realizingPair_addEquiv sigma T⟩, ?_⟩
  rintro g ⟨hsigma, hT⟩
  apply realizingPair_unique sigma T g hsigma
  intro v
  exact congrArg (fun e : (Fin d → K) ≃+ (Fin d → K) => e v) hT

end CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization
