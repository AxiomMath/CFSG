module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.ComponentClassification.CatalogueBHigherLinearInner

noncomputable section

open CatalogueBHigherLinearAction

universe u

instance pglFinite (n : ℕ) (K : Type u) [Field K] [Finite K] :
    Finite (Matrix.ProjGenLinGroup (Fin n) K) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

abbrev pglCentralizer (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :=
  Subgroup.centralizer ({a} : Set (Matrix.ProjGenLinGroup (Fin n) K))

abbrev localPSLRange (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) : Subgroup (pglCentralizer n K a) :=
  (pslRange n K).subgroupOf (pglCentralizer n K a)

instance localPSLRangeNormal (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) : (localPSLRange n K a).Normal := by
  change ((pslRange n K).comap (pglCentralizer n K a).subtype).Normal
  infer_instance

theorem pslRangeEquiv_pglAction (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :
    MulAut.congr (pslRangeEquiv n K) (pglAction n K a) =
      MulAut.conjNormal (H := pslRange n K) a := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
    (pglAction n K a ((pslRangeEquiv n K).symm x)) = a * x.val * a⁻¹
  rw [toPGL_pglAction, pslRangeEquiv_symm_toPGL]

@[expose] def fixedPSLCentralizerEquiv (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :
    FixedCommutingProduct.fixedSubgroup (pglAction n K a) ≃* localPSLRange n K a :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (pslRangeEquiv n K) (pglAction n K a)).trans
    ((MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
      (pslRangeEquiv_pglAction n K a))).trans
      (FixedNormalCentralizer.equivalence (pslRange n K) a).symm)

theorem fixedPSLCentralizerEquiv_val (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K)
    (x : FixedCommutingProduct.fixedSubgroup (pglAction n K a)) :
    (fixedPSLCentralizerEquiv n K a x).val.val =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x.val := rfl

theorem fixedPSLCentralizerEquiv_symm_toPGL (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) (x : localPSLRange n K a) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      ((fixedPSLCentralizerEquiv n K a).symm x).val = x.val.val := by
  have h := congrArg (fun y : localPSLRange n K a => y.val.val)
    ((fixedPSLCentralizerEquiv n K a).apply_symm_apply x)
  rw [fixedPSLCentralizerEquiv_val] at h
  exact h

theorem fixedPSL_eq_centralizer_comap (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :
    FixedCommutingProduct.fixedSubgroup (pglAction n K a) =
      (pglCentralizer n K a).comap Matrix.ProjectiveSpecialLinearGroup.toPGL := by
  ext x
  change pglAction n K a x = x ↔
    Matrix.ProjectiveSpecialLinearGroup.toPGL x ∈ pglCentralizer n K a
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h := toPGL_pglAction n K a x
    rw [hx] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  · intro hx
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPGL_pglAction, ← hx, mul_inv_cancel_right]

@[expose] def innerFixedCentralizerEquiv (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    FixedCommutingProduct.fixedSubgroup (innerDiagonalAction n K A) ≃*
      localPSLRange n K (Matrix.ProjGenLinGroup.mk A) :=
  fixedPSLCentralizerEquiv n K (Matrix.ProjGenLinGroup.mk A)

theorem innerFixedCentralizerEquiv_val (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (x : FixedCommutingProduct.fixedSubgroup (innerDiagonalAction n K A)) :
    (innerFixedCentralizerEquiv n K A x).val.val =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x.val := rfl

theorem pComponent_fixed_image (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) (p : ℕ)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (pglAction n K a)))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map (fixedPSLCentralizerEquiv n K a).toMonoidHom) :=
  CatalogueBAlternating.pComponent_map_equiv p (fixedPSLCentralizerEquiv n K a) L hL

theorem pComponent_fixed_extend (n : ℕ) (K : Type u) [Field K] [Finite K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (pglAction n K a)))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p
      ((L.map (fixedPSLCentralizerEquiv n K a).toMonoidHom).map
        (localPSLRange n K a).subtype) :=
  CatalogueBAlternating.pComponent_of_normal_subgroup p (localPSLRange n K a)
    (L.map (fixedPSLCentralizerEquiv n K a).toMonoidHom)
    (pComponent_fixed_image n K a p L hL)

theorem fixed_projection_hom (n : ℕ) (K : Type u) [Field K]
    (a : Matrix.ProjGenLinGroup (Fin n) K) :
    ((pglCentralizer n K a).subtype.comp (localPSLRange n K a).subtype).comp
        (fixedPSLCentralizerEquiv n K a).toMonoidHom =
      Matrix.ProjectiveSpecialLinearGroup.toPGL.comp
        (FixedCommutingProduct.fixedSubgroup (pglAction n K a)).subtype := by
  ext x
  rfl

end

end CFSG.ComponentClassification.CatalogueBHigherLinearInner
