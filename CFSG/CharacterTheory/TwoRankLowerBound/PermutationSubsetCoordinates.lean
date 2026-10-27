module

public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationCoefficientExtension
public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationFixedBasis

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def finiteFunctionSubsetEquiv {ring points : Type*} [CommRing ring]
    (subset : Set points) :
    (points → ring) ≃ₗ[ring] ((subset → ring) × ((subsetᶜ : Set points) → ring)) where
  toFun := fun value => (fun point => value point.val, fun point => value point.val)
  invFun := fun value point => if hmember : point ∈ subset then value.1 ⟨point, hmember⟩
    else value.2 ⟨point, hmember⟩
  left_inv := by
    intro value
    funext point
    dsimp only
    split_ifs <;> rfl
  right_inv := by
    intro value
    apply Prod.ext
    · funext point
      exact dite_eq_left point.property
    · funext point
      exact dite_eq_right point.property
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

noncomputable def permutationSubsetCoordinates {ring points : Type*}
    [CommRing ring] [Fintype points] (subset : Set points) :
    MonoidAlgebra ring points ≃ₗ[ring]
      (MonoidAlgebra ring subset × MonoidAlgebra ring (subsetᶜ : Set points)) :=
  (MonoidAlgebra.basis points ring).equivFun.trans
    ((finiteFunctionSubsetEquiv subset).trans
      (LinearEquiv.prodCongr (MonoidAlgebra.basis subset ring).equivFun.symm
        (MonoidAlgebra.basis (subsetᶜ : Set points) ring).equivFun.symm))

theorem monoidAlgebra_basis_equivFun_coeff {ring points : Type*} [CommRing ring] [Fintype points]
    (value : MonoidAlgebra ring points) (point : points) :
    (MonoidAlgebra.basis points ring).equivFun value point = value.coeff point := by
  rfl

theorem permutationSubsetCoordinates_fst_coeff {ring points : Type*}
    [CommRing ring] [Fintype points] (subset : Set points)
    (value : MonoidAlgebra ring points) (point : subset) :
    ((permutationSubsetCoordinates subset value).1).coeff point = value.coeff point.val := by
  change (MonoidAlgebra.basis subset ring).equivFun
    ((MonoidAlgebra.basis subset ring).equivFun.symm
      (fun member : subset => (MonoidAlgebra.basis points ring).equivFun value member.val)) point = _
  rw [LinearEquiv.apply_symm_apply, monoidAlgebra_basis_equivFun_coeff]

theorem permutationSubsetCoordinates_snd_coeff {ring points : Type*}
    [CommRing ring] [Fintype points] (subset : Set points)
    (value : MonoidAlgebra ring points) (point : (subsetᶜ : Set points)) :
    ((permutationSubsetCoordinates subset value).2).coeff point = value.coeff point.val := by
  change (MonoidAlgebra.basis (subsetᶜ : Set points) ring).equivFun
    ((MonoidAlgebra.basis (subsetᶜ : Set points) ring).equivFun.symm
      (fun member : (subsetᶜ : Set points) => (MonoidAlgebra.basis points ring).equivFun value member.val)) point = _
  rw [LinearEquiv.apply_symm_apply, monoidAlgebra_basis_equivFun_coeff]

theorem permutationSubsetCoordinates_symm_coeff_of_mem {ring points : Type*}
    [CommRing ring] [Fintype points] (subset : Set points)
    (value : MonoidAlgebra ring subset × MonoidAlgebra ring (subsetᶜ : Set points)) (point : subset) :
    ((permutationSubsetCoordinates subset).symm value).coeff point.val = value.1.coeff point := by
  have hequal := permutationSubsetCoordinates_fst_coeff subset
    ((permutationSubsetCoordinates subset).symm value) point
  rw [LinearEquiv.apply_symm_apply] at hequal
  exact hequal.symm

theorem permutationSubsetCoordinates_symm_coeff_of_not_mem {ring points : Type*}
    [CommRing ring] [Fintype points] (subset : Set points)
    (value : MonoidAlgebra ring subset × MonoidAlgebra ring (subsetᶜ : Set points))
    (point : (subsetᶜ : Set points)) :
    ((permutationSubsetCoordinates subset).symm value).coeff point.val = value.2.coeff point := by
  have hequal := permutationSubsetCoordinates_snd_coeff subset
    ((permutationSubsetCoordinates subset).symm value) point
  rw [LinearEquiv.apply_symm_apply] at hequal
  exact hequal.symm

theorem permutationSubsetCoordinates_symm_single_left {ring points : Type*}
    [CommRing ring] [Fintype points] (subset : Set points) (point : subset) :
    (permutationSubsetCoordinates (ring := ring) subset).symm (MonoidAlgebra.single point 1, 0) =
      MonoidAlgebra.single point.val 1 := by
  apply (permutationSubsetCoordinates subset).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext member
    simp only [permutationSubsetCoordinates_fst_coeff, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Subtype.val_inj]
  · ext member
    rw [permutationSubsetCoordinates_snd_coeff]
    have hne : point.val ≠ member.val := by
      intro hequal
      exact member.property (hequal ▸ point.property)
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ite_false,
      MonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem fixedBasisReduction_eq_leftCoordinate_residue {ring residue group points : Type*}
    [CommRing ring] [CommRing residue] [Group group] [MulAction group points] [Fintype points]
    (embedding : ring →+* residue) (operator : Module.End ring (MonoidAlgebra ring points)) :
    permutationCoefficientExtension embedding
      ((LinearMap.fst ring (MonoidAlgebra ring (MulAction.fixedPoints group points))
          (MonoidAlgebra ring ((MulAction.fixedPoints group points)ᶜ : Set points))).comp
        (((LinearEquiv.conjAlgEquiv ring (permutationSubsetCoordinates
            (MulAction.fixedPoints group points))) operator).comp
          (LinearMap.inl ring (MonoidAlgebra ring (MulAction.fixedPoints group points))
            (MonoidAlgebra ring ((MulAction.fixedPoints group points)ᶜ : Set points))))) =
      permutationFixedBasisReduction (group := group) embedding operator := by
  apply (MonoidAlgebra.basis (MulAction.fixedPoints group points) residue).ext
  intro column
  ext row
  have hequal := congrArg
    (fun matrix : Matrix (MulAction.fixedPoints group points) (MulAction.fixedPoints group points) residue =>
      matrix row column) (permutationCoefficientExtension_matrix embedding
        ((LinearMap.fst ring (MonoidAlgebra ring (MulAction.fixedPoints group points))
          (MonoidAlgebra ring ((MulAction.fixedPoints group points)ᶜ : Set points))).comp
          (((LinearEquiv.conjAlgEquiv ring (permutationSubsetCoordinates
              (MulAction.fixedPoints group points))) operator).comp
            (LinearMap.inl ring (MonoidAlgebra ring (MulAction.fixedPoints group points))
              (MonoidAlgebra ring ((MulAction.fixedPoints group points)ᶜ : Set points))))))
  simp only [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply, monoidAlgebra_basis_repr_coeff,
    RingHom.mapMatrix_apply, Matrix.map_apply] at hequal
  rw [MonoidAlgebra.basis_apply, permutationFixedBasisReduction_coeff, hequal]
  congr 1
  change ((permutationSubsetCoordinates (MulAction.fixedPoints group points))
    (operator ((permutationSubsetCoordinates (MulAction.fixedPoints group points)).symm
      (MonoidAlgebra.single column 1, 0)))).1.coeff row = _
  rw [permutationSubsetCoordinates_symm_single_left, permutationSubsetCoordinates_fst_coeff]

end CFSG.TwoRankLowerBound.Helpers
