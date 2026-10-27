module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import TauCeti.LinearAlgebra.Determinant

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBAlternatingIsometry

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem alternating_plane_det_identity (b : Module.Basis (Fin 2) K V)
    (B : BilinForm K V) (hB : B.IsAlt) (g : V →ₗ[K] V) (x y : V) :
    B (g x) (g y) = LinearMap.det g * B x y := by
  have h := LinearMap.IsAlt.compl₁₂_self_eq_det_smul b hB g
  simpa using LinearMap.congr_fun₂ h x y

theorem plane_isometry_iff_det (b : Module.Basis (Fin 2) K V)
    (B : BilinForm K V) (hB : B.IsAlt) (hBne : B ≠ 0) (g : V ≃ₗ[K] V) :
    g ∈ isometryGroup B ↔ LinearMap.det g.toLinearMap = 1 := by
  rw [mem_isometryGroup_iff]
  constructor
  · intro hg
    apply LinearMap.det_eq_of_compl₁₂_self_eq_smul b hB hBne
    ext x y
    simpa using hg x y
  · intro hg x y
    have h := alternating_plane_det_identity b B hB g.toLinearMap x y
    simpa only [LinearEquiv.coe_coe, hg, one_mul] using h

theorem plane_isometry_iff_matrix_det (b : Module.Basis (Fin 2) K V)
    (B : BilinForm K V) (hB : B.IsAlt) (hBne : B ≠ 0) (g : V ≃ₗ[K] V) :
    g ∈ isometryGroup B ↔
      basisMatrixEquiv b g ∈
        (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker := by
  rw [plane_isometry_iff_det b B hB hBne, MonoidHom.mem_ker, Units.ext_iff]
  change LinearMap.det g.toLinearMap = 1 ↔ (basisMatrixEquiv b g).val.det = 1
  rw [basisMatrixEquiv_val, LinearMap.det_toMatrix]

@[expose] def planeIsometryEquivSL (b : Module.Basis (Fin 2) K V)
    (B : BilinForm K V) (hB : B.IsAlt) (hBne : B ≠ 0) :
    isometryGroup B ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  ({ toFun := fun g =>
       ⟨basisMatrixEquiv b g.val, (plane_isometry_iff_matrix_det b B hB hBne _).mp g.property⟩
     invFun := fun A => ⟨(basisMatrixEquiv b).symm A.val,
       (plane_isometry_iff_matrix_det b B hB hBne _).mpr (by
         rw [MulEquiv.apply_symm_apply]
         exact A.property)⟩
     left_inv := fun g => Subtype.ext ((basisMatrixEquiv b).symm_apply_apply g.val)
     right_inv := fun A => Subtype.ext ((basisMatrixEquiv b).apply_symm_apply A.val)
     map_mul' := fun g h => Subtype.ext ((basisMatrixEquiv b).map_mul g.val h.val) } :
       isometryGroup B ≃*
         (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker).trans
    Matrix.SpecialLinearGroup.toGLKerEquiv.symm

theorem planeIsometryEquivSL_toGL (b : Module.Basis (Fin 2) K V)
    (B : BilinForm K V) (hB : B.IsAlt) (hBne : B ≠ 0) (g : isometryGroup B) :
    Matrix.SpecialLinearGroup.toGL (planeIsometryEquivSL b B hB hBne g) =
      basisMatrixEquiv b g.val := by
  apply Units.ext
  rfl

variable [FiniteDimensional K V]

@[expose] def planeBasis (hd : Module.finrank K V = 2) : Module.Basis (Fin 2) K V :=
  (Module.finBasis K V).reindex (finCongr hd)

theorem exists_planeIsometryEquivSL (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hd : Module.finrank K V = 2) :
    Nonempty (isometryGroup B ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K V)
  exact ⟨planeIsometryEquivSL (planeBasis hd) B hB hnd.ne_zero⟩

theorem plane_fieldThree_solvable [Finite K] (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hd : Module.finrank K V = 2) (hcard : Nat.card K = 3) :
    Group.IsSolvable (isometryGroup B) := by
  obtain ⟨e⟩ := exists_planeIsometryEquivSL B hB hnd hd
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.generalLinear_two_small_solvable K (Or.inr hcard)
  exact Group.isSolvable_of_isSolvable_injective
    (f := Matrix.SpecialLinearGroup.toGL.comp e.toMonoidHom)
    (Matrix.SpecialLinearGroup.toGL_injective.comp e.injective)

theorem plane_fieldThree_no_pComponent [Finite K] (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hd : Module.finrank K V = 2) (hcard : Nat.card K = 3)
    (p : ℕ) (L : Subgroup (isometryGroup B)) : ¬ CFSG.IsPComponent p L := by
  let : Group.IsSolvable (isometryGroup B) := plane_fieldThree_solvable B hB hnd hd hcard
  exact CatalogueBGeneralLinear.no_pComponent_of_solvable p L

end CFSG.ComponentClassification.CatalogueBAlternatingIsometry
