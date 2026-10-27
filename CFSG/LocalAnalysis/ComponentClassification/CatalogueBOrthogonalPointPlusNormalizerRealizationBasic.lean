module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometrySemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryPoints
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarKernelBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusNormalizerRealization

open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalPointData CatalogueBOrthogonalPointIsometry
open CatalogueBOrthogonalPointAction

universe u

variable {K : Type u} [Field K] {n : ℕ}

@[expose] def splitFieldEquiv (sigma : K ≃+* K) :
    (Fin n ⊕ Fin n → K) ≃ₛₗ[sigma.toRingHom] (Fin n ⊕ Fin n → K) where
  toFun := sCoord sigma
  invFun := sCoord sigma.symm
  left_inv := sCoord_symm_sCoord sigma
  right_inv := sCoord_sCoord_symm sigma
  map_add' := sCoord_add sigma
  map_smul' := sCoord_smul sigma

theorem splitFieldEquiv_apply (sigma : K ≃+* K) (v : Fin n ⊕ Fin n → K) :
    splitFieldEquiv sigma v = sCoord sigma v := rfl

theorem splitFieldEquiv_symm_apply (sigma : K ≃+* K) (v : Fin n ⊕ Fin n → K) :
    (splitFieldEquiv sigma).symm v = sCoord sigma.symm v := rfl

@[expose] def splitSemilinear (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) :
    (Fin n ⊕ Fin n → K) ≃ₛₗ[sigma.toRingHom] (Fin n ⊕ Fin n → K) :=
  { (splitFieldEquiv sigma).toAddEquiv.trans A.toAddEquiv with
    map_smul' c v := by
      change A (sCoord sigma (c • v)) = sigma c • A (sCoord sigma v)
      rw [sCoord_smul, A.map_smul] }

theorem splitSemilinear_apply
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (v : Fin n ⊕ Fin n → K) :
    splitSemilinear A sigma v = A (sCoord sigma v) := rfl

theorem splitSemilinear_symm_apply
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (v : Fin n ⊕ Fin n → K) :
    (splitSemilinear A sigma).symm v = sCoord sigma.symm (A.symm v) := rfl

theorem splitSemilinear_submodule
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (W : Submodule K (Fin n ⊕ Fin n → K)) :
    W.map (splitSemilinear A sigma).toLinearMap = semiImage A sigma W := by
  ext v
  rw [Submodule.mem_map_equiv, semiImage, Submodule.mem_map_equiv, mem_sCoordImage]
  rfl

theorem splitSemilinear_inverse_submodule
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (W : Submodule K (Fin n ⊕ Fin n → K)) :
    W.map (splitSemilinear A sigma).symm.toLinearMap = semiPreimage A sigma W := by
  ext v
  rw [Submodule.mem_map_equiv, semiPreimage, mem_sCoordImage, Submodule.mem_map_equiv]
  rfl

@[expose] def coordinateSemilinear
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) (sigma : K ≃+* K) :
    (Fin (2 * n) → K) ≃ₛₗ[sigma.toRingHom] (Fin (2 * n) → K) :=
  let e := (coordinatePlusIsometry n K).toLinearEquiv
  { (e.symm.toAddEquiv.trans (splitSemilinear A sigma).toAddEquiv).trans e.toAddEquiv with
    map_smul' c v := by
      change e (splitSemilinear A sigma (e.symm (c • v))) =
        sigma c • e (splitSemilinear A sigma (e.symm v))
      rw [e.symm.map_smul, (splitSemilinear A sigma).map_smulₛₗ, e.map_smul]
      rfl }

theorem coordinateSemilinear_apply
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (v : Fin (2 * n) → K) :
    coordinateSemilinear A sigma v =
      coordinatePlusIsometry n K (A (sCoord sigma ((coordinatePlusIsometry n K).symm v))) := rfl

theorem coordinateSemilinear_entry
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (v : Fin (2 * n) → K) (i : Fin (2 * n)) :
    coordinateSemilinear A sigma v i =
      A (fun j => sigma (v (plusIndexEquiv n j))) ((plusIndexEquiv n).symm i) := rfl

theorem coordinateSemilinear_symm_apply
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (v : Fin (2 * n) → K) :
    (coordinateSemilinear A sigma).symm v =
      coordinatePlusIsometry n K
        (sCoord sigma.symm (A.symm ((coordinatePlusIsometry n K).symm v))) := rfl

theorem coordinateSemilinear_symm_entry
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (v : Fin (2 * n) → K) (i : Fin (2 * n)) :
    (coordinateSemilinear A sigma).symm v i =
      sigma.symm (A.symm (fun j => v (plusIndexEquiv n j)) ((plusIndexEquiv n).symm i)) := rfl

theorem coordinateSemilinear_submodule
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (W : Submodule K (Fin (2 * n) → K)) :
    W.map (coordinateSemilinear A sigma).toLinearMap =
      (semiImage A sigma (W.map (coordinatePlusIsometry n K).symm.toLinearMap)).map
        (coordinatePlusIsometry n K).toLinearMap := by
  rw [← splitSemilinear_submodule]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨splitSemilinear A sigma ((coordinatePlusIsometry n K).symm x),
      ⟨(coordinatePlusIsometry n K).symm x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem coordinateSemilinear_inverse_submodule
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (W : Submodule K (Fin (2 * n) → K)) :
    W.map (coordinateSemilinear A sigma).symm.toLinearMap =
      (semiPreimage A sigma (W.map (coordinatePlusIsometry n K).symm.toLinearMap)).map
        (coordinatePlusIsometry n K).toLinearMap := by
  rw [← splitSemilinear_inverse_submodule]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(splitSemilinear A sigma).symm ((coordinatePlusIsometry n K).symm x),
      ⟨(coordinatePlusIsometry n K).symm x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem coordinateSemilinear_similarity
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))
    (sigma : K ≃+* K) (mu : Kˣ)
    (hA : ∀ v, quadPlus n K (A (sCoord sigma v)) = (mu : K) * sigma (quadPlus n K v))
    (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K (coordinateSemilinear A sigma v) =
      (mu : K) * sigma (coordinateQuadPlus n K v) := by
  rw [coordinateSemilinear_apply, (coordinatePlusIsometry n K).map_app,
    hA, (coordinatePlusIsometry n K).symm.map_app]

theorem coordinate_point_image_of_split_realization
    (A : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) (sigma : K ≃+* K)
    (phi : Equiv.Perm (Points (coordinateQuadPlus n K)))
    (hphi : ∀ L : Points (quadPlus n K),
      ((pointIsometryEquiv (coordinatePlusIsometry n K)).symm
        (phi (pointIsometryEquiv (coordinatePlusIsometry n K) L))).val =
          semiImage A sigma L.val) (L : Points (coordinateQuadPlus n K)) :
    (phi L).val = L.val.map (coordinateSemilinear A sigma).toLinearMap := by
  have h := hphi ((pointIsometryEquiv (coordinatePlusIsometry n K)).symm L)
  rw [Equiv.apply_symm_apply, pointIsometryEquiv_symm_submodule,
    pointIsometryEquiv_symm_submodule] at h
  rw [coordinateSemilinear_submodule, ← h]
  ext v
  constructor
  · intro hv
    exact ⟨(coordinatePlusIsometry n K).symm v, ⟨v, hv, rfl⟩,
      (coordinatePlusIsometry n K).apply_symm_apply v⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, hv⟩
    change coordinatePlusIsometry n K ((coordinatePlusIsometry n K).symm x) = v at hv
    rw [(coordinatePlusIsometry n K).apply_symm_apply] at hv
    exact hv ▸ hx

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusNormalizerRealization
