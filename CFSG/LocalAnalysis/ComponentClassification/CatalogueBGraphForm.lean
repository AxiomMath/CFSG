module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormParameters
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInner

public section

namespace CFSG.ComponentClassification.CatalogueBGraphForm

noncomputable section

open CatalogueBHigherLinearAction

universe u

theorem similitude_pComponent_quasisimple_of_isometries
    (n : ℕ) (K : Type u) [Field K] [Finite K] [Nonempty (Fin n)]
    (R : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (hI : ∀ J : Subgroup (isometryGroup n K R),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (similitudeGroup n K R)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  apply CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient
    p (isometryInSimilitude n K R) _ L hL
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (isometryInSimilitudeEquiv n K R) hI

theorem fixedPGL_pComponent_quasisimple_of_isometries
    (n : ℕ) (K : Type u) [Field K] [Finite K] [Nonempty (Fin n)]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (hI : ∀ J : Subgroup (isometryGroup n K A⁻¹),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (fixedPGL n K A)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L :=
  CatalogueBProjectiveInvolution.pComponent_quasisimple_of_central_surjection p
    (similitudeProjection n K A) (similitudeProjection_surjective n K A)
    (similitudeProjection_central_kernel n K A)
    (similitude_pComponent_quasisimple_of_isometries n K A⁻¹ p hI) L hL

theorem fixedPSL_pComponent_quasisimple_of_isometries
    (n : ℕ) (K : Type u) [Field K] [Finite K] [Nonempty (Fin n)]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (p : ℕ) [Fact p.Prime]
    (hI : ∀ J : Subgroup (isometryGroup n K A⁻¹),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (fixedPSL n K A)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  let e := fixedPSLEquivT n K A
  let M := L.map e.toMonoidHom
  have hextend := pComponent_fixed_extend n K A p L hL
  have hquasi := fixedPGL_pComponent_quasisimple_of_isometries n K A p hI
    (M.map (fixedT n K A).subtype) hextend
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((L.equivMapOfInjective e.toMonoidHom e.injective).trans
        (M.equivMapOfInjective (fixedT n K A).subtype (fixedT n K A).subtype_injective))
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem pure_graph_fixed_components_form_reduction
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (hodd : ringChar K ≠ 2)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (_hne : pureGraphAction n K A ≠ 1) (hsq : pureGraphAction n K A ^ 2 = 1) :
    (A.val.transpose = A.val ∨ (A.val.transpose = -A.val ∧ Even n)) ∧
      ∀ (p : ℕ), p.Prime →
        (∀ J : Subgroup (isometryGroup n K A⁻¹),
          CFSG.IsPComponent p J → CFSG.IsQuasisimple J) →
        ∀ L : Subgroup (fixedPSL n K A), CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  refine ⟨pureGraph_involution_form_data n K hn hodd A hsq, ?_⟩
  intro p hp hI L hL
  let : Fact p.Prime := ⟨hp⟩
  exact fixedPSL_pComponent_quasisimple_of_isometries n K A p hI L hL

@[expose] def scalarGraphAut (n : ℕ) (K : Type u) [Field K] :
    MulAut (CatalogueBHigherLinearInner.ScalarProjectiveSpecialLinear n K) :=
  MulAut.congr (CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K).symm
    (pslGraphAut n K)

theorem scalarGraphAut_mk (n : ℕ) (K : Type u) [Field K]
    (g : Matrix.SpecialLinearGroup (Fin n) K) :
    scalarGraphAut n K ((QuotientGroup.mk' (CatalogueBHigherLinearInner.slScalarCenter n K)) g) =
      (QuotientGroup.mk' (CatalogueBHigherLinearInner.slScalarCenter n K)) (g⁻¹).transpose := by
  let e := CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K
  apply e.injective
  change e (e.symm (pslGraphAut n K
    (e ((QuotientGroup.mk' (CatalogueBHigherLinearInner.slScalarCenter n K)) g)))) = _
  rw [MulEquiv.apply_symm_apply,
    CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv_mk,
    CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv_mk, pslGraphAut_mk]
  rfl

theorem scalarGraphAut_congr (n : ℕ) (K : Type u) [Field K] :
    MulAut.congr (CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K)
      (scalarGraphAut n K) = pslGraphAut n K := by
  apply MulEquiv.ext
  intro x
  let e := CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K
  change e (e.symm (pslGraphAut n K (e (e.symm x)))) = pslGraphAut n K x
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem scalarGraphAut_sq (n : ℕ) (K : Type u) [Field K] : scalarGraphAut n K ^ 2 = 1 := by
  let e := MulAut.congr (CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K)
  apply e.injective
  rw [map_pow, scalarGraphAut_congr, pslGraphAut_sq, map_one]

@[expose] def scalarPureGraphAction (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    MulAut (CatalogueBHigherLinearInner.ScalarProjectiveSpecialLinear n K) :=
  CatalogueBHigherLinearInner.scalarInnerDiagonalAction n K A * scalarGraphAut n K

theorem scalarPureGraphAction_mk (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    scalarPureGraphAction n K A ((QuotientGroup.mk' (CatalogueBHigherLinearInner.slScalarCenter n K)) g) =
      (QuotientGroup.mk' (CatalogueBHigherLinearInner.slScalarCenter n K))
        (slConjugation n K A (g⁻¹).transpose) := by
  change CatalogueBHigherLinearInner.scalarInnerDiagonalAction n K A
    (scalarGraphAut n K ((QuotientGroup.mk' (CatalogueBHigherLinearInner.slScalarCenter n K)) g)) = _
  rw [scalarGraphAut_mk, CatalogueBHigherLinearInner.scalarInnerDiagonalAction_mk]

theorem scalarPureGraphAction_congr (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    MulAut.congr (CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K)
      (scalarPureGraphAction n K A) = pureGraphAction n K A := by
  rw [scalarPureGraphAction, map_mul,
    CatalogueBHigherLinearInner.scalarInnerDiagonalAction_congr, scalarGraphAut_congr]
  rfl

@[expose] def scalarPureGraphFixedEquiv (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K) :
    TauCeti.fixedSubgroup (scalarPureGraphAction n K A).toMonoidHom ≃* fixedPSL n K A :=
  (CatalogueRelativeB.fixedSubgroupEquivalence
    (CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K)
    (scalarPureGraphAction n K A)).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        (scalarPureGraphAction_congr n K A)))

theorem scalarPureGraphFixedEquiv_val (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (x : TauCeti.fixedSubgroup (scalarPureGraphAction n K A).toMonoidHom) :
    (scalarPureGraphFixedEquiv n K A x).val =
      CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K x.val := rfl

theorem scalarPureGraph_involution_data (n : ℕ) (K : Type u) [Field K]
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : scalarPureGraphAction n K A ≠ 1) (hsq : scalarPureGraphAction n K A ^ 2 = 1) :
    pureGraphAction n K A ≠ 1 ∧ pureGraphAction n K A ^ 2 = 1 := by
  let e := MulAut.congr (CatalogueBHigherLinearInner.scalarProjectiveSpecialLinearEquiv n K)
  have haction : e (scalarPureGraphAction n K A) = pureGraphAction n K A :=
    scalarPureGraphAction_congr n K A
  constructor
  · intro h
    apply hne
    apply e.injective
    rw [haction, h, map_one]
  · rw [← haction, ← map_pow, hsq, map_one]

theorem pure_graph_scalar_fixed_components_form_reduction
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (hodd : ringChar K ≠ 2)
    (A : Matrix.GeneralLinearGroup (Fin n) K)
    (hne : scalarPureGraphAction n K A ≠ 1) (hsq : scalarPureGraphAction n K A ^ 2 = 1) :
    (A.val.transpose = A.val ∨ (A.val.transpose = -A.val ∧ Even n)) ∧
      ∀ (p : ℕ), p.Prime →
        (∀ J : Subgroup (isometryGroup n K A⁻¹),
          CFSG.IsPComponent p J → CFSG.IsQuasisimple J) →
        ∀ L : Subgroup (TauCeti.fixedSubgroup (scalarPureGraphAction n K A).toMonoidHom),
          CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  obtain ⟨hne', hsq'⟩ := scalarPureGraph_involution_data n K A hne hsq
  have hfull := pure_graph_fixed_components_form_reduction n K hn hodd A hne' hsq'
  refine ⟨hfull.1, ?_⟩
  intro p hp hI L hL
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (scalarPureGraphFixedEquiv n K A) (hfull.2 p hp hI) L hL

end

end CFSG.ComponentClassification.CatalogueBGraphForm
