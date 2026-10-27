module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponentsSpaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoSpaces

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryIsometry

universe u v

variable {E : Type u} [Field E] [Finite E] {V : Type v}
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {sigma : E ≃+* E} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)

theorem isometry_two_three_solvable
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hd : Module.finrank E V = 2)
    (hq : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) = 3) :
    Group.IsSolvable (isometryGroup h) := by
  obtain ⟨B, t, e, _⟩ :=
    CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
      sigma h hsym hnd hsigma hne hd
  let : Group.IsSolvable
      (Matrix.GeneralLinearGroup (Fin 2)
        (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) :=
    CatalogueBGeneralLinear.generalLinear_two_small_solvable _ (Or.inr hq)
  let : Group.IsSolvable
      (Matrix.SpecialLinearGroup (Fin 2)
        (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  let : Group.IsSolvable (specialIsometry h) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.isSolvable_of_subgroup_quotient (specialIsometry h)

theorem isometry_two_three_no_pComponent
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hd : Module.finrank E V = 2)
    (hq : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) = 3)
    (p : ℕ) (L : Subgroup (isometryGroup h)) : ¬ CFSG.IsPComponent p L := by
  let : Group.IsSolvable (isometryGroup h) :=
    isometry_two_three_solvable h hsym hnd hsigma hne hd hq
  exact CatalogueBGeneralLinear.no_pComponent_of_solvable p L

theorem specialIsometry_two_quasisimple
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hd : Module.finrank E V = 2)
    (hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 2)
    (hq3 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 3) :
    CFSG.IsQuasisimple (specialIsometry h) := by
  obtain ⟨B, t, e, _⟩ :=
    CatalogueBUnitaryTwo.exists_unitary_two_special_linear_isomorphism
      sigma h hsym hnd hsigma hne hd
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv e
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (CatalogueBGeneralLinear.specialLinear_quasisimple 2 _ le_rfl
          (Or.inr hq2) (Or.inr hq3))))

theorem isometry_two_pComponents
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hd : Module.finrank E V = 2)
    (hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 2)
    (hq3 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 3) :
    CFSG.IsQuasisimple (specialIsometry h) ∧
      ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup h),
        CFSG.IsPComponent p L → L = specialIsometry h ∧ CFSG.IsQuasisimple L := by
  have hquasi := specialIsometry_two_quasisimple h hsym hnd hsigma hne hd hq2 hq3
  exact ⟨hquasi, fun p hp L hL =>
    pComponent_eq_specialIsometry_of_quasisimple h hquasi p hp L hL⟩

end CFSG.ComponentClassification.CatalogueBUnitaryIsometry
