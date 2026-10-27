module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometrySpaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryIsometry

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

universe u v

variable {K : Type u} [Field K] [Finite K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {sigma : K ≃+* K} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K)

instance isometryGroupFinite : Finite (isometryGroup h) :=
  Finite.of_injective
    (fun g : isometryGroup h =>
      CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis K V) g.val)
    ((CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis K V)).injective.comp
      Subtype.val_injective)

theorem pComponent_eq_specialIsometry_of_quasisimple
    (hquasi : CFSG.IsQuasisimple (specialIsometry h)) (p : ℕ) (hp : p.Prime)
    (L : Subgroup (isometryGroup h)) (hL : CFSG.IsPComponent p L) :
    L = specialIsometry h ∧ CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hle, hrestricted⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient
      p (specialIsometry h) L hL
  let J := L.subgroupOf (specialIsometry h)
  let : Group.IsPerfect J := CatalogueBAlternating.pComponent_perfect hrestricted
  let : Nontrivial J := CatalogueBAlternating.pComponent_nontrivial hrestricted
  have htop : J = ⊤ :=
    (Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi) J
      (Components.chain_of_mathlib_subnormal hrestricted.choose_spec.2.1)).resolve_left
        (J.nontrivial_iff_ne_bot.mp inferInstance)
  have heq : L = specialIsometry h := le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
  exact ⟨heq, heq.symm ▸ hquasi⟩

omit [Finite K] in
theorem isometry_one_solvable (hd : Module.finrank K V = 1) :
    Group.IsSolvable (isometryGroup h) := by
  let b := (Module.finBasis K V).reindex (finCongr hd)
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 1) K) :=
    CatalogueBGeneralLinear.generalLinear_one_solvable K
  exact Group.isSolvable_of_isSolvable_injective
    (f := (CatalogueBAlternatingIsometry.basisMatrixEquiv b).toMonoidHom.comp
      (isometryGroup h).subtype)
    ((CatalogueBAlternatingIsometry.basisMatrixEquiv b).injective.comp
      (isometryGroup h).subtype_injective)

omit [Finite K] in
theorem isometry_one_no_pComponent (hd : Module.finrank K V = 1)
    (p : ℕ) (L : Subgroup (isometryGroup h)) : ¬ CFSG.IsPComponent p L := by
  let : Group.IsSolvable (isometryGroup h) := isometry_one_solvable h hd
  exact CatalogueBGeneralLinear.no_pComponent_of_solvable p L

theorem specialIsometry_quasisimple_of_three_le
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hd : 3 ≤ Module.finrank K V)
    (hnq : (Module.finrank K V,
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2)) :
    CFSG.IsQuasisimple (specialIsometry h) := by
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis h hsym hnd hsigma hne
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (specialIsometryMatrixEquiv h b hb)
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (SUid_quasisimple_finite sigma hsigma hne (Module.finrank K V) hd hnq)))

theorem isometry_pComponents_of_three_le
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hd : 3 ≤ Module.finrank K V)
    (hnq : (Module.finrank K V,
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2)) :
    CFSG.IsQuasisimple (specialIsometry h) ∧
      ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup h), CFSG.IsPComponent p L →
        L = specialIsometry h ∧ CFSG.IsQuasisimple L := by
  have hquasi := specialIsometry_quasisimple_of_three_le h hsym hnd hsigma hne hd hnq
  exact ⟨hquasi, fun p hp L hL => pComponent_eq_specialIsometry_of_quasisimple h hquasi p hp L hL⟩

end CFSG.ComponentClassification.CatalogueBUnitaryIsometry
