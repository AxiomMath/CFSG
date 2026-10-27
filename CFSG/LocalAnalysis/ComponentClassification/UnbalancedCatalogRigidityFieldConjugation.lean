module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldExtension
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthOddCore

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  mem_unitMultiplierPairs_iff)

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {R S : similarityPairs Q} (hRS : R * S = S * R)

section Conjugation

include hRS

theorem semilinear_symm_commute (y : Fin d → K) :
    (coordinateSemilinearMap R.val).symm (coordinateSemilinearMap S.val y) =
      coordinateSemilinearMap S.val ((coordinateSemilinearMap R.val).symm y) := by
  apply (coordinateSemilinearMap R.val).injective
  rw [AddEquiv.apply_symm_apply, semilinear_commute_of_mul_comm hRS, AddEquiv.apply_symm_apply]

theorem conj_mem_pairCentralizer {c : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hc : c ∈ pairCentralizer S) :
    matrixLinearIso (matrixConjugation R.val (matrixLinearIso.symm c)) ∈ pairCentralizer S := by
  have hcO : matrixLinearIso.symm c ∈ matrixIsometries Q := by
    change matrixLinearIso (matrixLinearIso.symm c) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [MulEquiv.apply_symm_apply]
    exact hc.1
  have hL : ∀ x, matrixLinearIso (matrixConjugation R.val (matrixLinearIso.symm c)) x =
      coordinateSemilinearMap R.val (c ((coordinateSemilinearMap R.val).symm x)) := by
    intro x
    change matrixLinearEquiv (matrixConjugation R.val (matrixLinearIso.symm c)) x = _
    rw [matrixConjugation_vector]
    change coordinateSemilinearMap R.val (matrixLinearIso (matrixLinearIso.symm c)
      ((coordinateSemilinearMap R.val).symm x)) = _
    rw [MulEquiv.apply_symm_apply]
  refine ⟨matrixConjugation_mem_isometries Q R _ hcO, fun v => ?_⟩
  rw [hL, hL, pairSemilinearMap_apply, pairSemilinearMap_apply, semilinear_symm_commute hRS]
  have h1 := hc.2 ((coordinateSemilinearMap R.val).symm v)
  rw [pairSemilinearMap_apply, pairSemilinearMap_apply] at h1
  rw [h1, semilinear_commute_of_mul_comm hRS]

@[expose] def conjPairCentralizer : pairCentralizer S →* pairCentralizer S :=
  ((matrixLinearIso.toMonoidHom.comp ((matrixConjugation R.val).toMonoidHom.comp
    matrixLinearIso.symm.toMonoidHom)).comp (pairCentralizer S).subtype).codRestrict _
      fun c => conj_mem_pairCentralizer hRS c.2

theorem conjPairCentralizer_val (c : pairCentralizer S) :
    (conjPairCentralizer hRS c : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearIso (matrixConjugation R.val (matrixLinearIso.symm c)) := rfl

variable {hS : S ∈ unitMultiplierPairs Q}
  (e : ↥(pairCentralizer S) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)))

@[expose] def conjDescent : ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) →*
    ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :=
  e.toMonoidHom.comp ((conjPairCentralizer hRS).comp e.symm.toMonoidHom)

theorem extHom_conjDescent (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :
    extHom e (conjDescent hRS e g) = matrixConjugation R.val (extHom e g) := by
  change matrixLinearIso.symm ((e.symm (e (conjPairCentralizer hRS (e.symm g))) :
    pairCentralizer S) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = _
  rw [MulEquiv.symm_apply_apply, conjPairCentralizer_val, MulEquiv.symm_apply_apply]
  rfl

theorem conjIsometry_extIsometry (g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :
    conjIsometry R (extIsometry e g) = extIsometry e (conjDescent hRS e g) :=
  Subtype.ext (extHom_conjDescent hRS e g).symm

theorem conjDescent_mem {g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)}
    (hg : (g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) ∈ pairDescentDerived hS) :
    (conjDescent hRS e g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) ∈
      pairDescentDerived hS :=
  mem_commutator_subtype_iff.mp
    (map_mem_commutator (conjDescent hRS e) (mem_commutator_subtype_iff.mpr hg))

end Conjugation

section Restrict

include hRS

theorem field_mul_comm : R.val.right * S.val.right = S.val.right * R.val.right :=
  congrArg (fun y : similarityPairs Q => y.val.right) hRS

@[expose] def restrictDescentField : descentField S.val.right ≃+* descentField S.val.right where
  toFun a := ⟨R.val.right a, mem_descentField.mpr (by
    have h := congrArg (fun τ : K ≃+* K => τ a) (field_mul_comm hRS)
    change R.val.right (S.val.right a) = S.val.right (R.val.right a) at h
    rw [← h, coe_descentField_fixed a])⟩
  invFun a := ⟨R.val.right.symm a, mem_descentField.mpr (by
    apply R.val.right.injective
    have h := congrArg (fun τ : K ≃+* K => τ (R.val.right.symm a)) (field_mul_comm hRS)
    change R.val.right (S.val.right (R.val.right.symm a)) =
      S.val.right (R.val.right (R.val.right.symm a)) at h
    rw [h, RingEquiv.apply_symm_apply, coe_descentField_fixed a])⟩
  left_inv a := Subtype.ext (R.val.right.symm_apply_apply (a : K))
  right_inv a := Subtype.ext (R.val.right.apply_symm_apply (a : K))
  map_mul' a b := Subtype.ext (map_mul R.val.right (a : K) b)
  map_add' a b := Subtype.ext (map_add R.val.right (a : K) b)

theorem coe_restrictDescentField (a : descentField S.val.right) :
    (restrictDescentField hRS a : K) = R.val.right a := rfl

theorem coordinateSemilinearMap_mem_pairFix {w : Fin d → K} (hw : w ∈ pairFix S) :
    coordinateSemilinearMap R.val w ∈ pairFix S := by
  have hw' : coordinateSemilinearMap S.val w = w := mem_fixSpace.mp hw
  rw [mem_fixSpace, pairSemilinearMap_apply, ← semilinear_commute_of_mul_comm hRS, hw']

@[expose] def restrictPairFix :
    pairFix S ≃ₛₗ[(restrictDescentField hRS).toRingHom] pairFix S where
  toFun w := ⟨coordinateSemilinearMap R.val w, coordinateSemilinearMap_mem_pairFix hRS w.2⟩
  invFun w := ⟨coordinateSemilinearMap R⁻¹.val w,
    coordinateSemilinearMap_mem_pairFix (Commute.inv_left hRS) w.2⟩
  map_add' w w' := Subtype.ext (map_add _ _ _)
  map_smul' c w := Subtype.ext (coordinateSemilinearMap_smul R.val (c : K) w)
  left_inv w := Subtype.ext (by
    change coordinateSemilinearMap R⁻¹.val (coordinateSemilinearMap R.val w) = w
    rw [Subgroup.coe_inv, coordinateSemilinearMap_inv, AddEquiv.symm_apply_apply])
  right_inv w := Subtype.ext (by
    change coordinateSemilinearMap R.val (coordinateSemilinearMap R⁻¹.val w) = w
    rw [Subgroup.coe_inv, coordinateSemilinearMap_inv, AddEquiv.apply_symm_apply])

theorem coe_restrictPairFix (w : pairFix S) :
    (restrictPairFix hRS w : Fin d → K) = coordinateSemilinearMap R.val w := rfl

theorem restrictPairFix_quad (hR : R ∈ unitMultiplierPairs Q) (hS : S ∈ unitMultiplierPairs Q)
    (w : pairFix S) :
    pairDescentForm hS (restrictPairFix hRS w) =
      restrictDescentField hRS (pairDescentForm hS w) :=
  Subtype.ext ((mem_unitMultiplierPairs_iff Q R).mp hR w)

theorem restrictPairFix_commute {hS : S ∈ unitMultiplierPairs Q}
    (e : ↥(pairCentralizer S) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)))
    (he : ∀ g w, (((e g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) :
      Fin d → K) = (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) w)
    {g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)}
    (hc : R * matrixIsometryInclusion Q (extIsometry e g) * R⁻¹ =
      matrixIsometryInclusion Q (extIsometry e g)) (w : pairFix S) :
    restrictPairFix hRS ((g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w) =
      (g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) (restrictPairFix hRS w) := by
  apply Subtype.ext
  rw [coe_restrictPairFix, ← extHom_mulVec e he g w, ← extHom_mulVec e he g,
    coe_restrictPairFix]
  exact semilinear_commute_of_conj_eq hc (w : Fin d → K)

end Restrict

end CFSG.ComponentClassification.UnbalancedCatalog
