module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem pComponent_quasisimple_of_equiv {X Y : Type*} [Group X] [Group Y]
    (p : ℕ) (e : X ≃* Y)
    (hY : ∀ M : Subgroup Y, CFSG.IsPComponent p M → CFSG.IsQuasisimple M)
    (L : Subgroup X) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have hmap := CatalogueBAlternating.pComponent_map_equiv p e L hL
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      (L.equivMapOfInjective e.toMonoidHom e.injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp (hY _ hmap)))

theorem pComponent_quasisimple_of_central_surjection {X Y : Type*}
    [Group X] [Finite X] [Group Y] [Finite Y]
    (p : ℕ) [Fact p.Prime] (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X)
    (hX : ∀ L : Subgroup X, CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (M : Subgroup Y) (hM : CFSG.IsPComponent p M) : CFSG.IsQuasisimple M := by
  obtain ⟨L, hL, hmap, _⟩ :=
    CatalogueBCentralQuotient.pComponent_exists_lift p f hsurjective hcentral M hM
  rw [← hmap]
  exact (CatalogueBCentralQuotient.pComponent_quasisimple_iff f hcentral p L hL).mp (hX L hL)

theorem ordinaryCentralizerProjection_rangeRestrict_kernel_central
    (A : Matrix.GeneralLinearGroup ι K) :
    (ordinaryCentralizerProjection A).rangeRestrict.ker ≤
      Subgroup.center (Subgroup.centralizer {A}) := by
  rw [MonoidHom.ker_rangeRestrict, ordinaryCentralizerProjection_kernel_eq_scalar]
  exact ordinaryCentralizerScalar_range_le_center A

@[expose] def projectiveCentralizerModuloOrdinaryEquiv [Nonempty ι]
    (A : Matrix.GeneralLinearGroup ι K) :
    letI := ordinaryCentralizerProjection_range_normal A
    (Subgroup.centralizer {Matrix.ProjGenLinGroup.mk A} ⧸
      (ordinaryCentralizerProjection A).range) ≃* (projectiveScalarCharacter A).range := by
  letI := ordinaryCentralizerProjection_range_normal A
  exact (QuotientGroup.quotientMulEquivOfEq (projectiveScalarCharacter_kernel_eq A).symm).trans
    (QuotientGroup.quotientKerEquivRange (projectiveScalarCharacter A))

theorem projectiveCentralizerModuloOrdinary_solvable [Nonempty ι]
    (A : Matrix.GeneralLinearGroup ι K) :
    letI := ordinaryCentralizerProjection_range_normal A
    Group.IsSolvable (Subgroup.centralizer {Matrix.ProjGenLinGroup.mk A} ⧸
      (ordinaryCentralizerProjection A).range) := by
  let := ordinaryCentralizerProjection_range_normal A
  exact Group.isSolvable_of_isSolvable_injective
    (f := (projectiveCentralizerModuloOrdinaryEquiv A).toMonoidHom)
    (projectiveCentralizerModuloOrdinaryEquiv A).injective

theorem projectiveCentralizer_pComponent_quasisimple_of_ordinary
    [Finite K] [Nonempty ι] (A : Matrix.GeneralLinearGroup ι K)
    (p : ℕ) [Fact p.Prime]
    (hordinary : ∀ J : Subgroup (Subgroup.centralizer {A}),
      CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup (Subgroup.centralizer {Matrix.ProjGenLinGroup.mk A}))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Fintype K := Fintype.ofFinite K
  let : Finite (Matrix.ProjGenLinGroup ι K) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  let := ordinaryCentralizerProjection_range_normal A
  let := projectiveCentralizerModuloOrdinary_solvable A
  apply CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient
    p (ordinaryCentralizerProjection A).range _ L hL
  exact pComponent_quasisimple_of_central_surjection p
    (ordinaryCentralizerProjection A).rangeRestrict
    (ordinaryCentralizerProjection A).rangeRestrict_surjective
    (ordinaryCentralizerProjection_rangeRestrict_kernel_central A) hordinary

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
