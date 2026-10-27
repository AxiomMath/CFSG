module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction

universe u

abbrev fixedPGL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (ProjGenLinGroup (Fin n) K) :=
  TauCeti.fixedSubgroup (pglGraphFieldAut n K sigma).toMonoidHom

abbrev fixedPSL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) K) :=
  TauCeti.fixedSubgroup (pslGraphFieldAut n K sigma).toMonoidHom

abbrev fixedT (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Subgroup (fixedPGL n K sigma) :=
  (pslRange n K).subgroupOf (fixedPGL n K sigma)

instance fixedTNormal (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    (fixedT n K sigma).Normal := by
  change ((pslRange n K).comap (fixedPGL n K sigma).subtype).Normal
  infer_instance

@[expose] def fixedPSLMap (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    fixedPSL n K sigma →* fixedT n K sigma where
  toFun x := ⟨⟨ProjectiveSpecialLinearGroup.toPGL x.val, by
    change pglGraphFieldAut n K sigma (ProjectiveSpecialLinearGroup.toPGL x.val) =
      ProjectiveSpecialLinearGroup.toPGL x.val
    rw [← toPGL_pslGraphFieldAut]
    exact congrArg ProjectiveSpecialLinearGroup.toPGL x.property⟩, ⟨x.val, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext (map_one _))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul _ x.val y.val))

theorem fixedPSLMap_bijective (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    Function.Bijective (fixedPSLMap n K sigma) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply ProjectiveSpecialLinearGroup.toPGL_injective
    exact congrArg (fun z : fixedT n K sigma => z.val.val) h
  · intro y
    obtain ⟨x, hx⟩ := y.property
    have hxfixed : pslGraphFieldAut n K sigma x = x := by
      apply ProjectiveSpecialLinearGroup.toPGL_injective
      rw [toPGL_pslGraphFieldAut, hx]
      exact y.val.property
    refine ⟨⟨x, hxfixed⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx

@[expose] def fixedPSLEquivT (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    fixedPSL n K sigma ≃* fixedT n K sigma :=
  MulEquiv.ofBijective (fixedPSLMap n K sigma) (fixedPSLMap_bijective n K sigma)

theorem fixedPSLEquivT_val (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : fixedPSL n K sigma) :
    (fixedPSLEquivT n K sigma x).val.val = ProjectiveSpecialLinearGroup.toPGL x.val := rfl

theorem fixedPSLEquivT_symm_toPGL (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K)
    (x : fixedT n K sigma) :
    ProjectiveSpecialLinearGroup.toPGL ((fixedPSLEquivT n K sigma).symm x).val =
      x.val.val := by
  have h := congrArg (fun y : fixedT n K sigma => y.val.val)
    ((fixedPSLEquivT n K sigma).apply_symm_apply x)
  rw [fixedPSLEquivT_val] at h
  exact h

theorem fixedPSL_eq_fixedPGL_comap (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    fixedPSL n K sigma = (fixedPGL n K sigma).comap
      ProjectiveSpecialLinearGroup.toPGL := by
  ext x
  change pslGraphFieldAut n K sigma x = x ↔
    pglGraphFieldAut n K sigma (ProjectiveSpecialLinearGroup.toPGL x) =
      ProjectiveSpecialLinearGroup.toPGL x
  constructor
  · intro h
    rw [← toPGL_pslGraphFieldAut, h]
  · intro h
    apply ProjectiveSpecialLinearGroup.toPGL_injective
    rwa [toPGL_pslGraphFieldAut]

theorem fixedPSL_map_eq_intersection (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) :
    (fixedPSL n K sigma).map ProjectiveSpecialLinearGroup.toPGL =
      pslRange n K ⊓ fixedPGL n K sigma := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    change pglGraphFieldAut n K sigma (ProjectiveSpecialLinearGroup.toPGL x) =
      ProjectiveSpecialLinearGroup.toPGL x
    rw [← toPGL_pslGraphFieldAut]
    exact congrArg ProjectiveSpecialLinearGroup.toPGL hx
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    change pslGraphFieldAut n K sigma x = x
    apply ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPGL_pslGraphFieldAut]
    exact hx

theorem fixed_projection_hom (n : ℕ) (K : Type u) [Field K] (sigma : K ≃+* K) :
    ((fixedPGL n K sigma).subtype.comp (fixedT n K sigma).subtype).comp
        (fixedPSLEquivT n K sigma).toMonoidHom =
      ProjectiveSpecialLinearGroup.toPGL.comp (fixedPSL n K sigma).subtype := by
  ext x
  rfl

theorem pComponent_fixed_image (n : ℕ) (K : Type u) [Field K]
    (sigma : K ≃+* K) (p : ℕ) (L : Subgroup (fixedPSL n K sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map (fixedPSLEquivT n K sigma).toMonoidHom) :=
  CatalogueBAlternating.pComponent_map_equiv p (fixedPSLEquivT n K sigma) L hL

theorem pComponent_fixed_extend (n : ℕ) (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) [Fact p.Prime] (L : Subgroup (fixedPSL n K sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p
      ((L.map (fixedPSLEquivT n K sigma).toMonoidHom).map (fixedT n K sigma).subtype) :=
  CatalogueBAlternating.pComponent_of_normal_subgroup p (fixedT n K sigma)
    (L.map (fixedPSLEquivT n K sigma).toMonoidHom) (pComponent_fixed_image n K sigma p L hL)

end

end CFSG.ComponentClassification.CatalogueBGraphField
