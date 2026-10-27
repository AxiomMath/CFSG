module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormProjection
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.ComponentClassification.CatalogueBGraphForm

noncomputable section

open CatalogueBHigherLinearAction

universe u

instance pglFinite (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K : Type u) [Field K] [Finite K] : Finite (Matrix.ProjGenLinGroup ι K) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

abbrev fixedPSL (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :=
  TauCeti.fixedSubgroup (pureGraphAction n K A).toMonoidHom

abbrev fixedT (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    Subgroup (fixedPGL n K A) :=
  (pslRange n K).subgroupOf (fixedPGL n K A)

instance fixedTNormal (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (fixedT n K A).Normal := by
  change ((pslRange n K).comap (fixedPGL n K A).subtype).Normal
  infer_instance

@[expose] def fixedPSLMap (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    fixedPSL n K A →* fixedT n K A where
  toFun x := ⟨⟨Matrix.ProjectiveSpecialLinearGroup.toPGL x.val, by
    change pglPureGraphAction n K A (Matrix.ProjectiveSpecialLinearGroup.toPGL x.val) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x.val
    rw [← toPGL_pureGraphAction]
    exact congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL x.property⟩, ⟨x.val, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul _ x.val y.val))

theorem fixedPSLMap_bijective (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    Function.Bijective (fixedPSLMap n K A) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    exact congrArg (fun z : fixedT n K A => z.val.val) h
  · intro y
    obtain ⟨x, hx⟩ := y.property
    have hxfixed : pureGraphAction n K A x = x := by
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [toPGL_pureGraphAction, hx]
      exact y.val.property
    refine ⟨⟨x, hxfixed⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

@[expose] def fixedPSLEquivT (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    fixedPSL n K A ≃* fixedT n K A :=
  MulEquiv.ofBijective (fixedPSLMap n K A) (fixedPSLMap_bijective n K A)

theorem fixedPSLEquivT_val (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K)
    (x : fixedPSL n K A) :
    (fixedPSLEquivT n K A x).val.val = Matrix.ProjectiveSpecialLinearGroup.toPGL x.val := rfl

theorem fixedPSLEquivT_symm_toPGL (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K)
    (x : fixedT n K A) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL ((fixedPSLEquivT n K A).symm x).val =
      x.val.val := by
  have h := congrArg (fun y : fixedT n K A => y.val.val)
    ((fixedPSLEquivT n K A).apply_symm_apply x)
  rw [fixedPSLEquivT_val] at h
  exact h

theorem fixedPSL_eq_fixedPGL_comap (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    fixedPSL n K A = (fixedPGL n K A).comap
      Matrix.ProjectiveSpecialLinearGroup.toPGL := by
  ext x
  change pureGraphAction n K A x = x ↔
    pglPureGraphAction n K A (Matrix.ProjectiveSpecialLinearGroup.toPGL x) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x
  constructor
  · intro h
    rw [← toPGL_pureGraphAction, h]
  · intro h
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rwa [toPGL_pureGraphAction]

theorem fixedPSL_map_eq_intersection (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    (fixedPSL n K A).map Matrix.ProjectiveSpecialLinearGroup.toPGL =
      pslRange n K ⊓ fixedPGL n K A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    change pglPureGraphAction n K A (Matrix.ProjectiveSpecialLinearGroup.toPGL x) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x
    rw [← toPGL_pureGraphAction]
    exact congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hx
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    change pureGraphAction n K A x = x
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPGL_pureGraphAction]
    exact hx

theorem fixed_projection_hom (n : ℕ) (K : Type u) [Field K] (A : Matrix.GeneralLinearGroup (Fin n) K) :
    ((fixedPGL n K A).subtype.comp (fixedT n K A).subtype).comp
        (fixedPSLEquivT n K A).toMonoidHom =
      Matrix.ProjectiveSpecialLinearGroup.toPGL.comp (fixedPSL n K A).subtype := by
  ext x
  rfl

theorem pComponent_fixed_image (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) (L : Subgroup (fixedPSL n K A))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map (fixedPSLEquivT n K A).toMonoidHom) :=
  CatalogueBAlternating.pComponent_map_equiv p (fixedPSLEquivT n K A) L hL

theorem pComponent_fixed_extend (n : ℕ) (K : Type u) [Field K] [Finite K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) [Fact p.Prime] (L : Subgroup (fixedPSL n K A))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p
      ((L.map (fixedPSLEquivT n K A).toMonoidHom).map (fixedT n K A).subtype) :=
  CatalogueBAlternating.pComponent_of_normal_subgroup p (fixedT n K A)
    (L.map (fixedPSLEquivT n K A).toMonoidHom) (pComponent_fixed_image n K A p L hL)

end

end CFSG.ComponentClassification.CatalogueBGraphForm
