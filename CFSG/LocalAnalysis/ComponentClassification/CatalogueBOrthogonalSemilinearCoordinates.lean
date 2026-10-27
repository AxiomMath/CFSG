module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix CatalogueBHigherLinearField

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def coordinateFieldMap (d : ℕ) (sigma : K ≃+* K) :
    (Fin d → K) ≃+ (Fin d → K) where
  toFun v i := sigma (v i)
  invFun v i := sigma.symm (v i)
  left_inv v := by funext i; exact sigma.symm_apply_apply (v i)
  right_inv v := by funext i; exact sigma.apply_symm_apply (v i)
  map_add' v w := by funext i; exact sigma.map_add (v i) (w i)

theorem coordinateFieldMap_apply (sigma : K ≃+* K) (v : Fin d → K) (i : Fin d) :
    coordinateFieldMap d sigma v i = sigma (v i) := rfl

theorem coordinateFieldMap_smul (sigma : K ≃+* K) (a : K) (v : Fin d → K) :
    coordinateFieldMap d sigma (a • v) = sigma a • coordinateFieldMap d sigma v := by
  funext i
  exact sigma.map_mul a (v i)

@[expose] def matrixLinearEquiv (A : GL (Fin d) K) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K)
    (GeneralLinearGroup.toLin A)

theorem matrixLinearEquiv_apply (A : GL (Fin d) K) (v : Fin d → K) :
    matrixLinearEquiv A v = A.val *ᵥ v := rfl

theorem matrixLinearEquiv_mul (A B : GL (Fin d) K) :
    matrixLinearEquiv (A * B) = matrixLinearEquiv A * matrixLinearEquiv B := by
  unfold matrixLinearEquiv
  rw [map_mul, map_mul]

theorem coordinateFieldMap_matrix (sigma : K ≃+* K) (A : GL (Fin d) K)
    (v : Fin d → K) :
    coordinateFieldMap d sigma (matrixLinearEquiv A v) =
      matrixLinearEquiv (glFieldAut (Fin d) K sigma A)
        (coordinateFieldMap d sigma v) := by
  funext i
  exact sigma.toRingHom.map_mulVec A.val v i

abbrev coordinateSemilinearGroup (d : ℕ) (K : Type u) [Field K] :=
  GL (Fin d) K ⋊[glFieldAut (Fin d) K] (K ≃+* K)

theorem coordinateSemilinearGroup_mul_matrix (g h : coordinateSemilinearGroup d K) :
    (g * h).left = g.left * glFieldAut (Fin d) K g.right h.left := rfl

theorem coordinateSemilinearGroup_mul_field (g h : coordinateSemilinearGroup d K) :
    (g * h).right = g.right * h.right := rfl

theorem coordinateSemilinearGroup_inv_matrix (g : coordinateSemilinearGroup d K) :
    g⁻¹.left = glFieldAut (Fin d) K g.right⁻¹ g.left⁻¹ := rfl

theorem coordinateSemilinearGroup_inv_field (g : coordinateSemilinearGroup d K) :
    g⁻¹.right = g.right⁻¹ := rfl

@[expose] def coordinateSemilinearMap (g : coordinateSemilinearGroup d K) :
    (Fin d → K) ≃+ (Fin d → K) :=
  (coordinateFieldMap d g.right).trans (matrixLinearEquiv g.left).toAddEquiv

theorem coordinateSemilinearMap_apply (g : coordinateSemilinearGroup d K)
    (v : Fin d → K) :
    coordinateSemilinearMap g v = g.left.val *ᵥ (fun i => g.right (v i)) := rfl

theorem coordinateSemilinearMap_smul (g : coordinateSemilinearGroup d K)
    (a : K) (v : Fin d → K) :
    coordinateSemilinearMap g (a • v) = g.right a • coordinateSemilinearMap g v := by
  change matrixLinearEquiv g.left (coordinateFieldMap d g.right (a • v)) = _
  rw [coordinateFieldMap_smul, LinearEquiv.map_smul]
  rfl

theorem coordinateSemilinearMap_mul (g h : coordinateSemilinearGroup d K)
    (v : Fin d → K) :
    coordinateSemilinearMap (g * h) v =
      coordinateSemilinearMap g (coordinateSemilinearMap h v) := by
  change matrixLinearEquiv (g.left * glFieldAut (Fin d) K g.right h.left)
      (coordinateFieldMap d (g.right * h.right) v) =
    matrixLinearEquiv g.left
      (coordinateFieldMap d g.right
        (matrixLinearEquiv h.left (coordinateFieldMap d h.right v)))
  rw [coordinateFieldMap_matrix, matrixLinearEquiv_mul, LinearEquiv.mul_apply]
  rfl

theorem coordinateSemilinearMap_one (v : Fin d → K) :
    coordinateSemilinearMap (1 : coordinateSemilinearGroup d K) v = v := by
  change (1 : Matrix (Fin d) (Fin d) K) *ᵥ v = v
  exact Matrix.one_mulVec v

theorem coordinateSemilinearMap_inv (g : coordinateSemilinearGroup d K) :
    coordinateSemilinearMap g⁻¹ = (coordinateSemilinearMap g).symm := by
  apply AddEquiv.ext
  intro v
  apply (coordinateSemilinearMap g).injective
  rw [AddEquiv.apply_symm_apply, ← coordinateSemilinearMap_mul, mul_inv_cancel,
    coordinateSemilinearMap_one]

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
