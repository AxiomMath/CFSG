module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open Matrix

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def coordinateSemilinearHom :
    coordinateSemilinearGroup d K →* Multiplicative (AddAut (Fin d → K)) where
  toFun := fun g => Multiplicative.ofAdd (coordinateSemilinearMap g)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply AddEquiv.ext
    exact coordinateSemilinearMap_one
  map_mul' g h := by
    apply congrArg Multiplicative.ofAdd
    apply AddEquiv.ext
    exact coordinateSemilinearMap_mul g h

theorem coordinateSemilinearMap_field_eq (hd : 1 ≤ d)
    (g h : coordinateSemilinearGroup d K)
    (heq : coordinateSemilinearMap g = coordinateSemilinearMap h) :
    g.right = h.right := by
  let i : Fin d := ⟨0, by omega⟩
  let w : Fin d → K := Pi.single i 1
  let v := (coordinateSemilinearMap g).symm w
  have hgv : coordinateSemilinearMap g v = w :=
    (coordinateSemilinearMap g).apply_symm_apply w
  have hhv : coordinateSemilinearMap h v = w := by rw [← heq]; exact hgv
  apply RingEquiv.ext
  intro a
  have ha := congrArg (fun f : (Fin d → K) ≃+ (Fin d → K) => f (a • v)) heq
  rw [coordinateSemilinearMap_smul, coordinateSemilinearMap_smul, hgv, hhv] at ha
  have hi := congrFun ha i
  simpa [w] using hi

theorem coordinateSemilinearMap_matrix_eq
    (g h : coordinateSemilinearGroup d K) (hfield : g.right = h.right)
    (heq : coordinateSemilinearMap g = coordinateSemilinearMap h) :
    g.left = h.left := by
  apply GeneralLinearGroup.toLin.injective
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K)).injective
  apply LinearEquiv.ext
  intro v
  let x := (coordinateFieldMap d g.right).symm v
  have hx := congrArg (fun f : (Fin d → K) ≃+ (Fin d → K) => f x) heq
  change matrixLinearEquiv g.left (coordinateFieldMap d g.right x) =
    matrixLinearEquiv h.left (coordinateFieldMap d h.right x) at hx
  rw [← hfield, AddEquiv.apply_symm_apply] at hx
  exact hx

theorem coordinateSemilinearHom_injective (hd : 1 ≤ d) :
    Function.Injective (coordinateSemilinearHom (d := d) (K := K)) := by
  intro g h heq
  have hmap : coordinateSemilinearMap g = coordinateSemilinearMap h :=
    congrArg Multiplicative.toAdd heq
  have hf := coordinateSemilinearMap_field_eq hd g h hmap
  exact SemidirectProduct.ext (coordinateSemilinearMap_matrix_eq g h hf hmap) hf

end CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
