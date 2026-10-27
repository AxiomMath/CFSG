module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldScalar

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearInner CatalogueBUnitaryIsometry

universe u

@[expose] def scalarProjection (n : ℕ) (K : Type u) [Field K] :
    GL (Fin n) K →* ScalarProjectiveGeneralLinear n K :=
  QuotientGroup.mk' (glScalarCenter n K)

theorem scalarProjection_native (n : ℕ) (K : Type u) [Field K] (g : GL (Fin n) K) :
    scalarProjectiveGeneralLinearEquiv n K (scalarProjection n K g) = ProjGenLinGroup.mk g :=
  scalarProjectiveGeneralLinearEquiv_mk n K g

@[expose] def scalarPSLInclusion (n : ℕ) (K : Type u) [Field K] :
    ScalarProjectiveSpecialLinear n K →* ScalarProjectiveGeneralLinear n K :=
  (scalarProjectiveGeneralLinearEquiv n K).symm.toMonoidHom.comp
    (ProjectiveSpecialLinearGroup.toPGL.comp (scalarProjectiveSpecialLinearEquiv n K).toMonoidHom)

theorem scalarPSLInclusion_native (n : ℕ) (K : Type u) [Field K]
    (x : ScalarProjectiveSpecialLinear n K) :
    scalarProjectiveGeneralLinearEquiv n K (scalarPSLInclusion n K x) =
      ProjectiveSpecialLinearGroup.toPGL (scalarProjectiveSpecialLinearEquiv n K x) :=
  (scalarProjectiveGeneralLinearEquiv n K).apply_symm_apply _

theorem scalarPSLInclusion_mk (n : ℕ) (K : Type u) [Field K]
    (g : SpecialLinearGroup (Fin n) K) :
    scalarPSLInclusion n K ((QuotientGroup.mk' (slScalarCenter n K)) g) =
      scalarProjection n K (SpecialLinearGroup.toGL g) := by
  apply (scalarProjectiveGeneralLinearEquiv n K).injective
  rw [scalarPSLInclusion_native, scalarProjectiveSpecialLinearEquiv_mk,
    scalarProjection_native]
  exact ProjectiveSpecialLinearGroup.toPGL_mk g

theorem scalarPSLInclusion_injective (n : ℕ) (K : Type u) [Field K] :
    Function.Injective (scalarPSLInclusion n K) :=
  (scalarProjectiveGeneralLinearEquiv n K).symm.injective.comp
    (ProjectiveSpecialLinearGroup.toPGL_injective.comp
      (scalarProjectiveSpecialLinearEquiv n K).injective)

abbrev scalarPSLRange (n : ℕ) (K : Type u) [Field K] :
    Subgroup (ScalarProjectiveGeneralLinear n K) := (scalarPSLInclusion n K).range

theorem scalarPSLRange_eq_original_image (n : ℕ) (K : Type u) [Field K] :
    scalarPSLRange n K = ((scalarProjection n K).comp SpecialLinearGroup.toGL).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (slScalarCenter n K) y
    exact ⟨g, (scalarPSLInclusion_mk n K g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(QuotientGroup.mk' (slScalarCenter n K)) g, scalarPSLInclusion_mk n K g⟩

theorem scalarPSLRange_eq_comap (n : ℕ) (K : Type u) [Field K] :
    scalarPSLRange n K = (pslRange n K).comap (scalarProjectiveGeneralLinearEquiv n K).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨scalarProjectiveSpecialLinearEquiv n K y, (scalarPSLInclusion_native n K y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨(scalarProjectiveSpecialLinearEquiv n K).symm y, ?_⟩
    apply (scalarProjectiveGeneralLinearEquiv n K).injective
    rw [scalarPSLInclusion_native, MulEquiv.apply_symm_apply]
    exact hy

instance scalarPSLRangeNormal (n : ℕ) (K : Type u) [Field K] : (scalarPSLRange n K).Normal := by
  rw [scalarPSLRange_eq_comap]
  infer_instance

theorem scalarPSLInclusion_graphField (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (x : ScalarProjectiveSpecialLinear n K) :
    scalarPSLInclusion n K (scalarGraphFieldAut n K sigma x) =
      scalarPGLGraphFieldAut n K sigma (scalarPSLInclusion n K x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (slScalarCenter n K) x
  rw [scalarGraphFieldAut_mk, scalarPSLInclusion_mk, scalarPSLInclusion_mk]
  change QuotientGroup.mk (SpecialLinearGroup.toGL (slGraphFieldAut n K sigma g)) =
    scalarPGLGraphFieldAut n K sigma (QuotientGroup.mk (SpecialLinearGroup.toGL g))
  rw [scalarPGLGraphFieldAut_mk, toGL_slGraphFieldAut]

abbrev scalarFixedPGL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :=
  TauCeti.fixedSubgroup (scalarPGLGraphFieldAut n K sigma).toMonoidHom

abbrev scalarFixedT (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (scalarFixedPGL n K sigma) :=
  (scalarPSLRange n K).subgroupOf (scalarFixedPGL n K sigma)

instance scalarFixedTNormal (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    (scalarFixedT n K sigma).Normal := by
  change ((scalarPSLRange n K).comap (scalarFixedPGL n K sigma).subtype).Normal
  infer_instance

@[expose] def scalarUnitaryProjection (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Uid sigma n →* scalarFixedPGL n K sigma :=
  (scalarFixedPGLEquiv n K sigma).symm.toMonoidHom.comp (unitaryProjection n K sigma)

theorem scalarUnitaryProjection_val (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (g : Uid sigma n) :
    (scalarUnitaryProjection n K sigma g).val = scalarProjection n K g.val := by
  apply (scalarProjectiveGeneralLinearEquiv n K).injective
  rw [scalarProjection_native]
  have h := congrArg Subtype.val
    ((scalarFixedPGLEquiv n K sigma).apply_symm_apply (unitaryProjection n K sigma g))
  rw [scalarFixedPGLEquiv_val, unitaryProjection_val] at h
  exact h

theorem scalarUnitaryProjection_surjective (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    Function.Surjective (scalarUnitaryProjection n K sigma) :=
  (scalarFixedPGLEquiv n K sigma).symm.surjective.comp
    (unitaryProjection_surjective n K hn sigma hsigma hne)

theorem scalarUnitaryProjection_kernel (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    (scalarUnitaryProjection n K sigma).ker = (unitaryProjection n K sigma).ker := by
  ext g
  change (scalarFixedPGLEquiv n K sigma).symm (unitaryProjection n K sigma g) = 1 ↔
    unitaryProjection n K sigma g = 1
  exact (scalarFixedPGLEquiv n K sigma).symm.map_eq_one_iff

theorem scalarUnitaryProjection_kernel_norm_one (n : ℕ) (K : Type u) [Field K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (g : Uid sigma n) :
    g ∈ (scalarUnitaryProjection n K sigma).ker ↔
      ∃ c : Kˣ, sigma (c : K) * (c : K) = 1 ∧
        GeneralLinearGroup.scalar (Fin n) c = g.val := by
  rw [scalarUnitaryProjection_kernel]
  exact unitaryProjection_kernel_norm_one n K hn sigma g

theorem scalarUnitaryProjection_central_kernel (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    (scalarUnitaryProjection n K sigma).ker ≤ Subgroup.center (Uid sigma n) := by
  rw [scalarUnitaryProjection_kernel]
  exact unitaryProjection_central_kernel n K sigma

theorem scalarFixedPGL_eq_unitary_image (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 1 ≤ n) (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    scalarFixedPGL n K sigma = (Uid sigma n).map (scalarProjection n K) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := scalarUnitaryProjection_surjective n K hn sigma hsigma hne ⟨x, hx⟩
    refine ⟨g.val, g.property, ?_⟩
    exact (scalarUnitaryProjection_val n K sigma g).symm.trans (congrArg Subtype.val hg)
  · rintro ⟨g, hg, rfl⟩
    have hx := (scalarUnitaryProjection n K sigma ⟨g, hg⟩).property
    rwa [scalarUnitaryProjection_val] at hx

@[expose] def scalarFixedTEquiv (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    scalarFixedT n K sigma ≃* fixedT n K sigma where
  toFun x := ⟨scalarFixedPGLEquiv n K sigma x.val, by
    change (scalarFixedPGLEquiv n K sigma x.val).val ∈ pslRange n K
    rw [scalarFixedPGLEquiv_val]
    have hx := x.property
    change x.val.val ∈ scalarPSLRange n K at hx
    rw [scalarPSLRange_eq_comap] at hx
    exact hx⟩
  invFun y := ⟨(scalarFixedPGLEquiv n K sigma).symm y.val, by
    change ((scalarFixedPGLEquiv n K sigma).symm y.val).val ∈ scalarPSLRange n K
    rw [scalarPSLRange_eq_comap]
    have h := y.property
    have he := congrArg Subtype.val ((scalarFixedPGLEquiv n K sigma).apply_symm_apply y.val)
    rw [scalarFixedPGLEquiv_val] at he
    change scalarProjectiveGeneralLinearEquiv n K
      ((scalarFixedPGLEquiv n K sigma).symm y.val).val ∈ pslRange n K
    rw [he]
    exact h⟩
  left_inv x := Subtype.ext ((scalarFixedPGLEquiv n K sigma).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((scalarFixedPGLEquiv n K sigma).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (map_mul (scalarFixedPGLEquiv n K sigma) x.val y.val)

@[expose] def scalarFixedPSLEquiv (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    TauCeti.fixedSubgroup (scalarGraphFieldAut n K sigma).toMonoidHom ≃* fixedPSL n K sigma :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (scalarProjectiveSpecialLinearEquiv n K)
    (scalarGraphFieldAut n K sigma)).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        (scalarGraphFieldAut_congr n K sigma)))

theorem scalarFixedPSLEquiv_val (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : TauCeti.fixedSubgroup (scalarGraphFieldAut n K sigma).toMonoidHom) :
    (scalarFixedPSLEquiv n K sigma x).val = scalarProjectiveSpecialLinearEquiv n K x.val := rfl

@[expose] def scalarFixedPSLEquivT (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    TauCeti.fixedSubgroup (scalarGraphFieldAut n K sigma).toMonoidHom ≃* scalarFixedT n K sigma :=
  (scalarFixedPSLEquiv n K sigma).trans
    ((fixedPSLEquivT n K sigma).trans (scalarFixedTEquiv n K sigma).symm)

theorem scalarFixedPSLEquivT_val (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K)
    (x : TauCeti.fixedSubgroup (scalarGraphFieldAut n K sigma).toMonoidHom) :
    (scalarFixedPSLEquivT n K sigma x).val.val = scalarPSLInclusion n K x.val := by
  apply (scalarProjectiveGeneralLinearEquiv n K).injective
  rw [scalarPSLInclusion_native]
  have h := congrArg (fun y : fixedT n K sigma => y.val.val)
    ((scalarFixedTEquiv n K sigma).apply_symm_apply
      (fixedPSLEquivT n K sigma (scalarFixedPSLEquiv n K sigma x)))
  rw [fixedPSLEquivT_val, scalarFixedPSLEquiv_val] at h
  change scalarProjectiveGeneralLinearEquiv n K
      (scalarFixedPSLEquivT n K sigma x).val.val =
    ProjectiveSpecialLinearGroup.toPGL (scalarProjectiveSpecialLinearEquiv n K x.val) at h
  exact h

end

end CFSG.ComponentClassification.CatalogueBGraphField
