module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometrySpaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

universe u

variable {E : Type u} [Field E] (sigma : E ≃+* E)

abbrev fixedSpecialLinear : Subgroup (SpecialLinearGroup (Fin 2) E) :=
  TauCeti.fixedSubgroup (CatalogueBHigherLinearField.slFieldAut (Fin 2) E sigma).toMonoidHom

theorem mem_fixedSpecialLinear_iff (M : SpecialLinearGroup (Fin 2) E) :
    M ∈ fixedSpecialLinear sigma ↔ ∀ i j, sigma (M.val i j) = M.val i j := by
  change CatalogueBHigherLinearField.slFieldAut (Fin 2) E sigma M = M ↔ _
  constructor
  · intro h i j
    exact congrFun₂ (congrArg Subtype.val h) i j
  · intro h
    apply Subtype.ext
    ext i j
    exact h i j

@[expose] def fixedSLMap :
    SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma) →*
      SpecialLinearGroup (Fin 2) E :=
  SpecialLinearGroup.map (CatalogueBLinearTwoDescent.fixedSubfield E sigma).subtype

theorem fixedSLMap_entry
    (M : SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma))
    (i j : Fin 2) : (fixedSLMap sigma M).val i j = (M.val i j : E) := rfl

theorem fixedSLMap_injective : Function.Injective (fixedSLMap sigma) := by
  intro M N h
  apply Subtype.ext
  ext i j
  exact congrFun₂ (congrArg Subtype.val h) i j

@[expose] def fixedSLRestrict (M : fixedSpecialLinear sigma) :
    SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma) := by
  let A : Matrix (Fin 2) (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma) :=
    fun i j => ⟨M.val.val i j,
      (CatalogueBLinearTwoDescent.mem_fixedSubfield E sigma _).mpr
        ((mem_fixedSpecialLinear_iff sigma M.val).mp M.property i j)⟩
  refine ⟨A, ?_⟩
  apply (CatalogueBLinearTwoDescent.fixedSubfield E sigma).subtype.injective
  rw [map_one, RingHom.map_det]
  change M.val.val.det = 1
  exact M.val.property

theorem fixedSLMap_restrict (M : fixedSpecialLinear sigma) :
    fixedSLMap sigma (fixedSLRestrict sigma M) = M.val := by
  apply Subtype.ext
  rfl

@[expose] def fixedSLInclusionEquiv :
    SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≃*
      fixedSpecialLinear sigma where
  toFun M := ⟨fixedSLMap sigma M, by
    rw [mem_fixedSpecialLinear_iff]
    intro i j
    exact (CatalogueBLinearTwoDescent.mem_fixedSubfield E sigma _).mp (M.val i j).property⟩
  invFun := fixedSLRestrict sigma
  left_inv M := by
    apply fixedSLMap_injective sigma
    exact fixedSLMap_restrict sigma _
  right_inv M := Subtype.ext (fixedSLMap_restrict sigma M)
  map_mul' M N := Subtype.ext (map_mul (fixedSLMap sigma) M N)

theorem fixedSLInclusionEquiv_val
    (M : SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) :
    (fixedSLInclusionEquiv sigma M).val = fixedSLMap sigma M := rfl

@[expose] def hyperbolicSpecialLinear : Subgroup (SpecialLinearGroup (Fin 2) E) :=
  (CatalogueBUnitaryIsometry.isometryGroup (hyperbolicForm sigma)).comap
    SpecialLinearGroup.toLin'

theorem mem_hyperbolicSpecialLinear_iff (M : SpecialLinearGroup (Fin 2) E) :
    M ∈ hyperbolicSpecialLinear sigma ↔
      ∀ x y, hyperbolicForm sigma (M.val *ᵥ x) (M.val *ᵥ y) =
        hyperbolicForm sigma x y := Iff.rfl

@[expose] def hyperbolicSLFixedEquiv (t : Eˣ) (ht : sigma (t : E) = -(t : E)) :
    hyperbolicSpecialLinear sigma ≃* fixedSpecialLinear sigma where
  toFun M := ⟨diagonalConjugation t M.val,
    (mem_fixedSpecialLinear_iff sigma _).mpr
      ((hyperbolic_iff_conjugation_fixed sigma t ht M.val).mp M.property)⟩
  invFun M := ⟨(diagonalConjugation t).symm M.val, by
    rw [mem_hyperbolicSpecialLinear_iff, hyperbolic_iff_conjugation_fixed sigma t ht,
      MulEquiv.apply_symm_apply]
    exact (mem_fixedSpecialLinear_iff sigma M.val).mp M.property⟩
  left_inv M := Subtype.ext ((diagonalConjugation t).symm_apply_apply M.val)
  right_inv M := Subtype.ext ((diagonalConjugation t).apply_symm_apply M.val)
  map_mul' M N := Subtype.ext ((diagonalConjugation t).map_mul M.val N.val)

@[expose] def hyperbolicSLEquiv (t : Eˣ) (ht : sigma (t : E) = -(t : E)) :
    hyperbolicSpecialLinear sigma ≃*
      SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma) :=
  (hyperbolicSLFixedEquiv sigma t ht).trans (fixedSLInclusionEquiv sigma).symm

theorem hyperbolicSLEquiv_forward (t : Eˣ) (ht : sigma (t : E) = -(t : E))
    (M : hyperbolicSpecialLinear sigma) :
    (fixedSLMap sigma (hyperbolicSLEquiv sigma t ht M)).val =
      (diagonalGL t)⁻¹.val * M.val.val * (diagonalGL t).val := by
  have h := congrArg Subtype.val
    ((fixedSLInclusionEquiv sigma).apply_symm_apply (hyperbolicSLFixedEquiv sigma t ht M))
  change fixedSLMap sigma (hyperbolicSLEquiv sigma t ht M) =
    diagonalConjugation t M.val at h
  rw [h, diagonalConjugation_val]

theorem hyperbolicSLEquiv_inverse (t : Eˣ) (ht : sigma (t : E) = -(t : E))
    (N : SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) :
    ((hyperbolicSLEquiv sigma t ht).symm N).val.val =
      (diagonalGL t).val * (fixedSLMap sigma N).val * (diagonalGL t)⁻¹.val := by
  have h := hyperbolicSLEquiv_forward sigma t ht ((hyperbolicSLEquiv sigma t ht).symm N)
  rw [MulEquiv.apply_symm_apply] at h
  have hD : (diagonalGL t).val * (diagonalGL t)⁻¹.val = 1 := (diagonalGL t).mul_inv
  calc
    ((hyperbolicSLEquiv sigma t ht).symm N).val.val =
        ((diagonalGL t).val * (diagonalGL t)⁻¹.val) *
          ((hyperbolicSLEquiv sigma t ht).symm N).val.val *
          ((diagonalGL t).val * (diagonalGL t)⁻¹.val) := by
      rw [hD, Matrix.one_mul, Matrix.mul_one]
    _ = (diagonalGL t).val *
        ((diagonalGL t)⁻¹.val * ((hyperbolicSLEquiv sigma t ht).symm N).val.val *
          (diagonalGL t).val) * (diagonalGL t)⁻¹.val := by
      simp only [Matrix.mul_assoc]
    _ = (diagonalGL t).val * (fixedSLMap sigma N).val * (diagonalGL t)⁻¹.val := by
      rw [← h]

end CFSG.ComponentClassification.CatalogueBUnitaryTwo
