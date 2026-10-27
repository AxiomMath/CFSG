module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPlaneMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open QuadraticMap LinearMap
open CatalogueBAlternatingIsometry
open scoped Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem specialOrthogonal_two_comm (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : Q.polarBilin.Nondegenerate) (hd : Module.finrank K V = 2)
    (g k : specialOrthogonalWithin Q) : g * k = k * g := by
  let : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨c, hc⟩ := BilinForm.exists_orthogonal_basis (B := Q.polarBilin)
    (BilinForm.isSymm_iff.mp Q.isSymm_polarBilin)
  let b := c.reindex (finCongr hd)
  have hb : Q.polarBilin.IsOrthoᵢ b := by
    intro i j hij
    change Q.polarBilin (b i) (b j) = 0
    simpa only [b, Module.Basis.reindex_apply] using
      hc (fun heq => hij ((finCongr hd).symm.injective heq))
  let a := Q.polarBilin (b 0) (b 0)
  let d := Q.polarBilin (b 1) (b 1)
  have ha : a ≠ 0 := hb.not_isOrtho_basis_self_of_separatingLeft hQ.1 0
  have hgram : BilinForm.toMatrix b Q.polarBilin = planeGram a d := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [BilinForm.toMatrix_apply, planeGram, a]
    · simpa [BilinForm.toMatrix_apply, planeGram] using hb (i := 0) (j := 1) (by decide)
    · simpa [BilinForm.toMatrix_apply, planeGram] using hb (i := 1) (j := 0) (by decide)
    · simp [BilinForm.toMatrix_apply, planeGram, d]
  have hdet (x : specialOrthogonalWithin Q) :
      (basisMatrixEquiv b x.val.val).val.det = 1 := by
    rw [basisMatrixEquiv_val, LinearMap.det_toMatrix]
    have hx := congrArg Units.val (mem_specialOrthogonalWithin_iff.mp x.property)
    simpa only [LinearEquiv.coe_det, Units.val_one] using hx
  have hmatrix (x : specialOrthogonalWithin Q) :
      (basisMatrixEquiv b x.val.val).valᵀ * planeGram a d *
        (basisMatrixEquiv b x.val.val).val = planeGram a d := by
    rw [← hgram]
    apply (isometry_iff_matrix b Q.polarBilin x.val.val).mp
    rw [mem_isometryGroup_iff]
    exact fun u v => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.val.property u v
  apply Subtype.ext
  apply Subtype.ext
  apply (basisMatrixEquiv b).injective
  apply Units.ext
  change ((basisMatrixEquiv b) (g.val.val * k.val.val)).val =
    ((basisMatrixEquiv b) (k.val.val * g.val.val)).val
  rw [map_mul, map_mul]
  exact plane_matrices_commute a d ha _ _ (hdet g) (hdet k) (hmatrix g) (hmatrix k)

theorem orthogonal_two_solvable (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : Q.polarBilin.Nondegenerate) (hd : Module.finrank K V = 2) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  let : Group.IsSolvable (specialOrthogonalWithin Q) :=
    Group.isSolvable_of_comm (specialOrthogonal_two_comm Q h2 hQ hd)
  exact Group.isSolvable_of_ker_le_range (specialOrthogonalWithin Q).subtype (orthogonalDet Q)
    (fun g hg => ⟨⟨g, mem_specialOrthogonalWithin_iff.mpr
      ((orthogonalDet_apply g).symm.trans ((orthogonalDet Q).mem_ker.mp hg))⟩, rfl⟩)

theorem orthogonal_zero_solvable (Q : QuadraticForm K V) (hd : Module.finrank K V = 0) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  let : Subsingleton V := Module.finrank_zero_iff.mp hd
  apply Group.isSolvable_of_comm
  intro g k
  exact Subtype.ext (LinearEquiv.ext (fun v => Subsingleton.elim _ _))

theorem orthogonal_one_solvable (Q : QuadraticForm K V) (hd : Module.finrank K V = 1) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  let b := (Module.finBasis K V).reindex (finCongr hd)
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 1) K) :=
    CatalogueBGeneralLinear.generalLinear_one_solvable K
  exact Group.isSolvable_of_isSolvable_injective
    (f := (basisMatrixEquiv b).toMonoidHom.comp
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype)
    ((basisMatrixEquiv b).injective.comp
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective)

theorem orthogonal_small_solvable (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : Q.polarBilin.Nondegenerate) (hd : Module.finrank K V ≤ 2) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  by_cases hzero : Module.finrank K V = 0
  · exact orthogonal_zero_solvable Q hzero
  by_cases hone : Module.finrank K V = 1
  · exact orthogonal_one_solvable Q hone
  exact orthogonal_two_solvable Q h2 hQ (by omega)

theorem orthogonal_small_no_pComponent (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (hQ : Q.polarBilin.Nondegenerate) (hd : Module.finrank K V ≤ 2)
    (p : ℕ) (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    ¬ CFSG.IsPComponent p L := by
  let : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    orthogonal_small_solvable Q h2 hQ hd
  exact CatalogueBGeneralLinear.no_pComponent_of_solvable p L

end CFSG.ComponentClassification.CatalogueBOrthogonal
