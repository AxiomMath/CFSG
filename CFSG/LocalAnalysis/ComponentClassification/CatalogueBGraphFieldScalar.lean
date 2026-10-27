module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphForm

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearField
open CatalogueBHigherLinearInner

universe u

abbrev glScalarCenter (n : ℕ) (K : Type u) [Field K] : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range

theorem glScalarCenter_eq_center (n : ℕ) (K : Type u) [Field K] :
    glScalarCenter n K = Subgroup.center (GL (Fin n) K) :=
  GeneralLinearGroup.center_eq_range_scalar.symm

instance glScalarCenterNormal (n : ℕ) (K : Type u) [Field K] : (glScalarCenter n K).Normal := by
  rw [glScalarCenter_eq_center]
  infer_instance

abbrev ScalarProjectiveGeneralLinear (n : ℕ) (K : Type u) [Field K] :=
  GL (Fin n) K ⧸ glScalarCenter n K

@[expose] def scalarProjectiveGeneralLinearEquiv (n : ℕ) (K : Type u) [Field K] :
    ScalarProjectiveGeneralLinear n K ≃* ProjGenLinGroup (Fin n) K :=
  QuotientGroup.quotientMulEquivOfEq (glScalarCenter_eq_center n K)

theorem scalarProjectiveGeneralLinearEquiv_mk (n : ℕ) (K : Type u) [Field K]
    (g : GL (Fin n) K) :
    scalarProjectiveGeneralLinearEquiv n K (QuotientGroup.mk g) = ProjGenLinGroup.mk g :=
  QuotientGroup.quotientMulEquivOfEq_mk (glScalarCenter_eq_center n K) g

@[expose] def scalarPGLGraphFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (ScalarProjectiveGeneralLinear n K) :=
  MulAut.congr (scalarProjectiveGeneralLinearEquiv n K).symm (pglGraphFieldAut n K sigma)

theorem scalarPGLGraphFieldAut_mk (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : GL (Fin n) K) :
    scalarPGLGraphFieldAut n K sigma (QuotientGroup.mk g) =
      QuotientGroup.mk (glGraphFieldAut n K sigma g) := by
  let e := scalarProjectiveGeneralLinearEquiv n K
  apply e.injective
  change e (e.symm (pglGraphFieldAut n K sigma (e (QuotientGroup.mk g)))) = _
  rw [MulEquiv.apply_symm_apply, scalarProjectiveGeneralLinearEquiv_mk,
    scalarProjectiveGeneralLinearEquiv_mk, pglGraphFieldAut_mk]

theorem scalarPGLGraphFieldAut_congr (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut.congr (scalarProjectiveGeneralLinearEquiv n K) (scalarPGLGraphFieldAut n K sigma) =
      pglGraphFieldAut n K sigma := by
  ext x
  let e := scalarProjectiveGeneralLinearEquiv n K
  change e (e.symm (pglGraphFieldAut n K sigma (e (e.symm x)))) = pglGraphFieldAut n K sigma x
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem scalarPGLGraphFieldAut_sq (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) :
    scalarPGLGraphFieldAut n K sigma ^ 2 = 1 := by
  let e := MulAut.congr (scalarProjectiveGeneralLinearEquiv n K)
  apply e.injective
  rw [map_pow, scalarPGLGraphFieldAut_congr, pglGraphFieldAut_sq_eq_one n K sigma hsigma, map_one]

@[expose] def scalarFixedPGLEquiv (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    TauCeti.fixedSubgroup (scalarPGLGraphFieldAut n K sigma).toMonoidHom ≃* fixedPGL n K sigma :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (scalarProjectiveGeneralLinearEquiv n K)
    (scalarPGLGraphFieldAut n K sigma)).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        (scalarPGLGraphFieldAut_congr n K sigma)))

theorem scalarFixedPGLEquiv_val (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : TauCeti.fixedSubgroup (scalarPGLGraphFieldAut n K sigma).toMonoidHom) :
    (scalarFixedPGLEquiv n K sigma x).val = scalarProjectiveGeneralLinearEquiv n K x.val := rfl

@[expose] def scalarFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (ScalarProjectiveSpecialLinear n K) :=
  MulAut.congr (scalarProjectiveSpecialLinearEquiv n K).symm (pslFieldAut (Fin n) K sigma)

theorem scalarFieldAut_mk (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    scalarFieldAut n K sigma ((QuotientGroup.mk' (slScalarCenter n K)) g) =
      (QuotientGroup.mk' (slScalarCenter n K)) (slFieldAut (Fin n) K sigma g) := by
  let e := scalarProjectiveSpecialLinearEquiv n K
  apply e.injective
  change e (e.symm (pslFieldAut (Fin n) K sigma
    (e ((QuotientGroup.mk' (slScalarCenter n K)) g)))) = _
  rw [MulEquiv.apply_symm_apply, scalarProjectiveSpecialLinearEquiv_mk,
    scalarProjectiveSpecialLinearEquiv_mk]
  exact pslFieldAut_mk (Fin n) K sigma g

theorem scalarFieldAut_congr (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut.congr (scalarProjectiveSpecialLinearEquiv n K) (scalarFieldAut n K sigma) =
      pslFieldAut (Fin n) K sigma := by
  ext x
  let e := scalarProjectiveSpecialLinearEquiv n K
  change e (e.symm (pslFieldAut (Fin n) K sigma (e (e.symm x)))) = pslFieldAut (Fin n) K sigma x
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

@[expose] def scalarGraphFieldAut (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut (ScalarProjectiveSpecialLinear n K) :=
  scalarFieldAut n K sigma * CatalogueBGraphForm.scalarGraphAut n K

theorem scalarGraphFieldAut_mk (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    scalarGraphFieldAut n K sigma ((QuotientGroup.mk' (slScalarCenter n K)) g) =
      (QuotientGroup.mk' (slScalarCenter n K)) (slGraphFieldAut n K sigma g) := by
  change scalarFieldAut n K sigma (CatalogueBGraphForm.scalarGraphAut n K
    ((QuotientGroup.mk' (slScalarCenter n K)) g)) = _
  rw [CatalogueBGraphForm.scalarGraphAut_mk, scalarFieldAut_mk]
  rfl

theorem scalarGraphFieldAut_congr (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    MulAut.congr (scalarProjectiveSpecialLinearEquiv n K) (scalarGraphFieldAut n K sigma) =
      pslGraphFieldAut n K sigma := by
  rw [scalarGraphFieldAut, map_mul, scalarFieldAut_congr, CatalogueBGraphForm.scalarGraphAut_congr]
  rfl

@[expose] def scalarGraphFieldAction (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) : MulAut (ScalarProjectiveSpecialLinear n K) :=
  scalarInnerDiagonalAction n K A * scalarGraphFieldAut n K sigma

theorem scalarGraphFieldAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) (g : SpecialLinearGroup (Fin n) K) :
    scalarGraphFieldAction n K A sigma ((QuotientGroup.mk' (slScalarCenter n K)) g) =
      (QuotientGroup.mk' (slScalarCenter n K)) (slConjugation n K A (slGraphFieldAut n K sigma g)) := by
  change scalarInnerDiagonalAction n K A (scalarGraphFieldAut n K sigma
    ((QuotientGroup.mk' (slScalarCenter n K)) g)) = _
  rw [scalarGraphFieldAut_mk, scalarInnerDiagonalAction_mk]

theorem scalarGraphFieldAction_congr (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) :
    MulAut.congr (scalarProjectiveSpecialLinearEquiv n K) (scalarGraphFieldAction n K A sigma) =
      graphFieldAction n K A sigma := by
  rw [scalarGraphFieldAction, map_mul, scalarInnerDiagonalAction_congr, scalarGraphFieldAut_congr]
  rfl

theorem scalarGraphField_involution_data (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K)
    (hne : scalarGraphFieldAction n K A sigma ≠ 1)
    (hsquare : scalarGraphFieldAction n K A sigma ^ 2 = 1) :
    graphFieldAction n K A sigma ≠ 1 ∧ graphFieldAction n K A sigma ^ 2 = 1 := by
  let e := MulAut.congr (scalarProjectiveSpecialLinearEquiv n K)
  have haction := scalarGraphFieldAction_congr n K A sigma
  constructor
  · intro h
    apply hne
    apply e.injective
    rw [haction, h, map_one]
  · rw [← haction, ← map_pow, hsquare, map_one]

@[expose] def scalarGraphFieldFixedEquiv (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) :
    TauCeti.fixedSubgroup (scalarGraphFieldAction n K A sigma).toMonoidHom ≃*
      twistedFixedPSL n K A sigma :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (scalarProjectiveSpecialLinearEquiv n K)
    (scalarGraphFieldAction n K A sigma)).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        (scalarGraphFieldAction_congr n K A sigma)))

theorem scalarGraphFieldFixedEquiv_val (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K)
    (x : TauCeti.fixedSubgroup (scalarGraphFieldAction n K A sigma).toMonoidHom) :
    (scalarGraphFieldFixedEquiv n K A sigma x).val = scalarProjectiveSpecialLinearEquiv n K x.val := rfl

end

end CFSG.ComponentClassification.CatalogueBGraphField
