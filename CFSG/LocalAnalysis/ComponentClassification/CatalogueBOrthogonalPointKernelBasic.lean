module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarKernel

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel

open Matrix CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalPointAction CatalogueBOrthogonalScalarKernel

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def coordinateSemilinearEquiv (g : coordinateSemilinearGroup d K) :
    (Fin d → K) ≃ₛₗ[g.right.toRingHom] (Fin d → K) :=
  { coordinateSemilinearMap g, coordinateSemilinearLinearMap g with }

theorem coordinateSemilinearEquiv_apply (g : coordinateSemilinearGroup d K)
    (v : Fin d → K) : coordinateSemilinearEquiv g v = coordinateSemilinearMap g v := rfl

theorem coordinateSemilinearEquiv_toLinearMap (g : coordinateSemilinearGroup d K) :
    (coordinateSemilinearEquiv g).toLinearMap = coordinateSemilinearLinearMap g := rfl

theorem coordinateSemilinearEquiv_symm_apply (g : coordinateSemilinearGroup d K)
    (v : Fin d → K) :
    (coordinateSemilinearEquiv g).symm v = coordinateSemilinearMap g⁻¹ v := by
  rw [coordinateSemilinearMap_inv]
  rfl

theorem coordinateSemilinearEquiv_similarity (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (v : Fin d → K) :
    Q (coordinateSemilinearEquiv g.val v) = (multiplier Q g : K) * g.val.right (Q v) :=
  multiplier_spec Q g v

theorem similarityPointAction_eq_one_iff_lines (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) :
    similarityPointAction Q g = 1 ↔ FixesSingularLines Q (coordinateSemilinearEquiv g.val) := by
  constructor
  · intro h W hW hsing
    exact congrArg
      (fun e : Equiv.Perm (Points Q) => (e ⟨W, hW, hsing⟩).val) h
  · intro h
    apply Equiv.ext
    intro L
    apply Subtype.ext
    exact h L.val L.property.1 L.property.2

theorem coordinateMap_of_scalarMatrix (g : coordinateSemilinearGroup d K)
    (hfield : g.right = 1) (a : Kˣ)
    (ha : GeneralLinearGroup.scalar (Fin d) a = g.left) (v : Fin d → K) :
    coordinateSemilinearMap g v = (a : K) • v := by
  have hg : g = SemidirectProduct.inl (GeneralLinearGroup.scalar (Fin d) a) :=
    SemidirectProduct.ext ha.symm hfield
  rw [hg, coordinateSemilinearMap_inl, scalarMatrixLinearEquiv]

theorem scalarMatrix_eq_of_coordinateMap (g : coordinateSemilinearGroup d K)
    (hfield : g.right = 1) (a : Kˣ)
    (ha : ∀ v, coordinateSemilinearMap g v = (a : K) • v) :
    GeneralLinearGroup.scalar (Fin d) a = g.left := by
  apply GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K)).injective
  apply LinearEquiv.ext
  intro v
  change matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) a) v = matrixLinearEquiv g.left v
  rw [scalarMatrixLinearEquiv]
  have hg : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hfield
  have hv := (ha v).symm
  rw [hg, coordinateSemilinearMap_inl] at hv
  exact hv

theorem similarityPointAction_of_scalarMatrix (Q : QuadraticForm K (Fin d → K))
    (g : similarityPairs Q) (hfield : g.val.right = 1) (a : Kˣ)
    (ha : GeneralLinearGroup.scalar (Fin d) a = g.val.left) :
    similarityPointAction Q g = 1 := by
  apply (similarityPointAction_eq_one_iff_lines Q g).mpr
  exact fixesSingularLines_of_scalar (coordinateSemilinearEquiv g.val) a
    (coordinateMap_of_scalarMatrix g.val hfield a ha)

end CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel
