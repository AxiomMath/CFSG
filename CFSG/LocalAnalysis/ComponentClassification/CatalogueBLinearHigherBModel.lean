module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponentsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBLinearHigherB

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CatalogueBHigherLinearAction CatalogueBHigherLinearField CatalogueBGraphForm

universe u

@[expose] def nativeEquiv (n : ℕ) (K : Type u) [Field K] :
    LinearFlag.projectiveSL n K ≃* ProjectiveSpecialLinearGroup (Fin n) K :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm

variable {n : ℕ} {K : Type u} [Field K]

theorem nativeEquiv_proj (g : SpecialLinearGroup (Fin n) K) :
    nativeEquiv n K (LinearFlag.proj n K g) = QuotientGroup.mk g := by
  apply (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).injective
  rw [nativeEquiv, MulEquiv.apply_symm_apply]
  rfl

theorem congr_eq_of_proj {α : MulAut (LinearFlag.projectiveSL n K)}
    {β : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)}
    (h : ∀ g, nativeEquiv n K (α (LinearFlag.proj n K g)) = β (QuotientGroup.mk g)) :
    MulAut.congr (nativeEquiv n K) α = β := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← nativeEquiv_proj,
    MulEquiv.symm_apply_apply]
  exact h g

theorem congr_conjAut (A : GL (Fin n) K) :
    MulAut.congr (nativeEquiv n K) (LinearFlag.conjAut n K A) = innerDiagonalAction n K A :=
  congr_eq_of_proj fun g => by
    rw [LinearFlag.conjAut_proj, nativeEquiv_proj]
    exact (innerDiagonalAction_mk n K A g).symm

theorem congr_fieldAut (σ : K ≃+* K) :
    MulAut.congr (nativeEquiv n K) (LinearFlag.fieldAut n K σ) = pslFieldAut (Fin n) K σ :=
  congr_eq_of_proj fun g => by
    rw [LinearFlag.fieldAut_proj, nativeEquiv_proj, pslFieldAut_mk]

theorem congr_dualAut :
    MulAut.congr (nativeEquiv n K) (LinearFlag.dualAut n K) = pslGraphAut n K :=
  congr_eq_of_proj fun g => by
    rw [LinearFlag.dualAut_proj, nativeEquiv_proj, pslGraphAut_mk_inverseTranspose]

theorem congr_semilinear (A : GL (Fin n) K) (σ : K ≃+* K) :
    MulAut.congr (nativeEquiv n K) (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ) =
      CatalogueBLinearSemilinear.semilinearAction n K A σ := by
  rw [map_mul, congr_conjAut, congr_fieldAut]
  rfl

theorem congr_graphField (A : GL (Fin n) K) (σ : K ≃+* K) :
    MulAut.congr (nativeEquiv n K)
        (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ * LinearFlag.dualAut n K) =
      CatalogueBGraphField.graphFieldAction n K A σ := by
  rw [map_mul, congr_semilinear, congr_dualAut,
    CatalogueBGraphField.graphFieldAction_eq_semilinear_graph]

theorem congr_pureGraph (A : GL (Fin n) K) :
    MulAut.congr (nativeEquiv n K) (LinearFlag.conjAut n K A * LinearFlag.dualAut n K) =
      pureGraphAction n K A := by
  rw [map_mul, congr_conjAut, congr_dualAut]
  rfl

theorem congr_involution {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {α : MulAut X}
    (hne : α ≠ 1) (hsq : α ^ 2 = 1) : MulAut.congr e α ≠ 1 ∧ MulAut.congr e α ^ 2 = 1 :=
  ⟨fun h => hne ((MulAut.congr e).injective (h.trans (map_one _).symm)),
    by rw [← map_pow, hsq, map_one]⟩

theorem fixed_pComponent_quasisimple_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {α : MulAut X} {β : MulAut Y} (h : MulAut.congr e α = β) (p : ℕ)
    (hβ : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup β),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup α)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L :=
  CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    ((CatalogueRelativeB.fixedSubgroupEquivalence e α).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup h))) hβ L hL

end CFSG.ComponentClassification.CatalogueBLinearHigherB
