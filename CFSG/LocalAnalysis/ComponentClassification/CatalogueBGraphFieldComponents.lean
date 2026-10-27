module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldSpecialUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponents

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBUnitaryIsometry CatalogueBHigherLinearAction

universe u

theorem fixedPGL_pComponent_specialUnitary (n : ℕ) (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hn : 3 ≤ n)
    (hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2))
    (p : ℕ) (hp : p.Prime) (M : Subgroup (fixedPGL n K sigma))
    (hM : CFSG.IsPComponent p M) :
    M = (specialUnitaryProjection n K sigma).range ∧ CFSG.IsQuasisimple M := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨J, hJ, hmap, _⟩ := CatalogueBCentralQuotient.pComponent_exists_lift p
    (unitaryProjection n K sigma) (unitaryProjection_surjective n K (by omega) sigma hsigma hne)
    (unitaryProjection_central_kernel n K sigma) M hM
  obtain ⟨hJeq, hJquasi⟩ := (unitary_isometry_p_components sigma hsigma hne n hn hnq).2 p hp J hJ
  constructor
  · rw [← hmap, hJeq, ← specialUnitaryProjection_range]
  · rw [← hmap]
    exact (CatalogueBCentralQuotient.pComponent_quasisimple_iff (unitaryProjection n K sigma)
      (unitaryProjection_central_kernel n K sigma) p J hJ).mp hJquasi

theorem fixedPSL_pComponent_projectiveSpecialUnitary (n : ℕ) (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hn : 3 ≤ n)
    (hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2))
    (p : ℕ) (hp : p.Prime) (L : Subgroup (fixedPSL n K sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L ∧ Nonempty (L ≃* ProjectiveSpecialUnitary n K sigma) := by
  let : Fact p.Prime := ⟨hp⟩
  let e := fixedPSLEquivT n K sigma
  let M := L.map e.toMonoidHom
  let N := M.map (fixedT n K sigma).subtype
  have hN : CFSG.IsPComponent p N := pComponent_fixed_extend n K sigma p L hL
  obtain ⟨hNeq, hNquasi⟩ := fixedPGL_pComponent_specialUnitary n K sigma hsigma hne hn hnq p hp N hN
  let eLN : L ≃* N := (L.equivMapOfInjective e.toMonoidHom e.injective).trans
    (M.equivMapOfInjective (fixedT n K sigma).subtype (fixedT n K sigma).subtype_injective)
  refine ⟨CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv eLN (CatalogueBAlternating.quasisimple_iff_native.mp hNquasi)), ?_⟩
  exact ⟨(eLN.trans (MulEquiv.subgroupCongr hNeq)).trans
    (projectiveSpecialUnitaryEquivImage n K sigma).symm⟩

abbrev twistedFixedPSL (n : ℕ) (K : Type u) [Field K]
    (A : GL (Fin n) K) (sigma : K ≃+* K) :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) K) :=
  TauCeti.fixedSubgroup (graphFieldAction n K A sigma).toMonoidHom

theorem innerDiagonal_congr_graphField (n : ℕ) (K : Type u) [Field K]
    (H : GL (Fin n) K) (sigma : K ≃+* K) :
    MulAut.congr (innerDiagonalAction n K H) (pslGraphFieldAut n K sigma) =
      innerDiagonalAction n K H * pslGraphFieldAut n K sigma *
        (innerDiagonalAction n K H)⁻¹ := by
  ext x
  rfl

@[expose] def graphFieldFixedConjugacyEquiv (n : ℕ) (K : Type u) [Field K]
    (A H : GL (Fin n) K) (sigma : K ≃+* K)
    (hconj : graphFieldAction n K A sigma = innerDiagonalAction n K H *
      pslGraphFieldAut n K sigma * (innerDiagonalAction n K H)⁻¹) :
    fixedPSL n K sigma ≃* twistedFixedPSL n K A sigma :=
  (CatalogueRelativeB.fixedSubgroupEquivalence (innerDiagonalAction n K H)
    (pslGraphFieldAut n K sigma)).trans
      (MulEquiv.subgroupCongr (congrArg FixedCommutingProduct.fixedSubgroup
        ((innerDiagonal_congr_graphField n K H sigma).trans hconj.symm)))

theorem graphFieldFixedConjugacyEquiv_val (n : ℕ) (K : Type u) [Field K]
    (A H : GL (Fin n) K) (sigma : K ≃+* K)
    (hconj : graphFieldAction n K A sigma = innerDiagonalAction n K H *
      pslGraphFieldAut n K sigma * (innerDiagonalAction n K H)⁻¹)
    (x : fixedPSL n K sigma) :
    (graphFieldFixedConjugacyEquiv n K A H sigma hconj x).val = innerDiagonalAction n K H x.val := rfl

theorem graphField_involution_fixed_pComponent_projectiveSpecialUnitary
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (hn : 3 ≤ n) (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (hsquare : graphFieldAction n K A sigma ^ 2 = 1)
    (hnq : (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2))
    (p : ℕ) (hp : p.Prime) (L : Subgroup (twistedFixedPSL n K A sigma))
    (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L ∧ Nonempty (L ≃* ProjectiveSpecialUnitary n K sigma) := by
  obtain ⟨hsigma, H, hH⟩ := graphField_involution_conjugacy n K hn A sigma hne hsquare
  let e := (graphFieldFixedConjugacyEquiv n K A H sigma hH).symm
  let M := L.map e.toMonoidHom
  have hM : CFSG.IsPComponent p M := CatalogueBAlternating.pComponent_map_equiv p e L hL
  obtain ⟨hMquasi, ⟨eM⟩⟩ := fixedPSL_pComponent_projectiveSpecialUnitary n K sigma hsigma hne hn hnq p hp M hM
  let eL := L.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv eL (CatalogueBAlternating.quasisimple_iff_native.mp hMquasi)),
    ⟨eL.trans eM⟩⟩

end

end CFSG.ComponentClassification.CatalogueBGraphField
