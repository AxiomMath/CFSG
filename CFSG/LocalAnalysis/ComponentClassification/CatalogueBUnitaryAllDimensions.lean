module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensionsTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryIsometry

universe u v

variable {E : Type u} [Field E] [Finite E] {V : Type v}
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {sigma : E ≃+* E} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)

theorem isometry_all_dimensions_small
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hsmall : Module.finrank E V = 1 ∨
      Module.finrank E V = 2 ∧
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) = 3) :
    Group.IsSolvable (isometryGroup h) ∧
      ∀ (p : ℕ) (L : Subgroup (isometryGroup h)), ¬ CFSG.IsPComponent p L := by
  have hsol : Group.IsSolvable (isometryGroup h) := by
    rcases hsmall with hd | ⟨hd, hq⟩
    · exact isometry_one_solvable h hd
    · exact isometry_two_three_solvable h hsym hnd hsigma hne hd hq
  let : Group.IsSolvable (isometryGroup h) := hsol
  exact ⟨hsol, CatalogueBGeneralLinear.no_pComponent_of_solvable⟩

theorem isometry_all_dimensions_nonsmall
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hn : 1 ≤ Module.finrank E V)
    (hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 2)
    (hn1 : Module.finrank E V ≠ 1)
    (hnq : (Module.finrank E V,
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) ≠ (2, 3)) :
    CFSG.IsQuasisimple (specialIsometry h) ∧
      ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup h),
        CFSG.IsPComponent p L → L = specialIsometry h ∧ CFSG.IsQuasisimple L := by
  by_cases hn2 : Module.finrank E V = 2
  · have hq3 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 3 := by
      intro hq3
      exact hnq (Prod.ext hn2 hq3)
    exact isometry_two_pComponents h hsym hnd hsigma hne hn2 hq2 hq3
  · have hdim : 3 ≤ Module.finrank E V := by omega
    exact isometry_pComponents_of_three_le h hsym hnd hsigma hne hdim
      (fun heq => hq2 (congrArg Prod.snd heq))

theorem isometry_all_dimensions_pComponent_quasisimple
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hn : 1 ≤ Module.finrank E V)
    (hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) ≠ 2)
    (p : ℕ) (hp : p.Prime) (L : Subgroup (isometryGroup h))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  by_cases hn1 : Module.finrank E V = 1
  · exact (isometry_one_no_pComponent h hn1 p L hL).elim
  by_cases hnq : (Module.finrank E V,
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) = (2, 3)
  · exact (isometry_two_three_no_pComponent h hsym hnd hsigma hne
      (congrArg Prod.fst hnq) (congrArg Prod.snd hnq) p L hL).elim
  · exact ((isometry_all_dimensions_nonsmall h hsym hnd hsigma hne hn hq2 hn1 hnq).2
      p hp L hL).2

end CFSG.ComponentClassification.CatalogueBUnitaryIsometry

namespace CFSG.ComponentClassification.CatalogueBUnitaryTwo

open CatalogueBUnitaryIsometry

universe u v

variable {E : Type u} [Field E] [Finite E] {V : Type v}
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem odd_unitary_all_dimensional_isometry_p_components
    (r f : ℕ) [Fact r.Prime] (hr : r ≠ 2) (hf : 1 ≤ f)
    (hE : Nat.card E = (r ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation r f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hn : 1 ≤ Module.finrank E V) :
    (∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup h),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    ((Module.finrank E V = 1 ∨ (Module.finrank E V, r ^ f) = (2, 3)) →
      Group.IsSolvable (isometryGroup h) ∧
        ∀ (p : ℕ) (L : Subgroup (isometryGroup h)), ¬ CFSG.IsPComponent p L) ∧
    ((Module.finrank E V ≠ 1 ∧ (Module.finrank E V, r ^ f) ≠ (2, 3)) →
      CFSG.IsQuasisimple (specialIsometry h) ∧
        ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup h),
          CFSG.IsPComponent p L → L = specialIsometry h) := by
  obtain ⟨hsigma, hne, hfixed⟩ := unitaryFieldConjugation_data r f hE
  have hr3 : 3 ≤ r := by
    have := (Fact.out : r.Prime).two_le
    omega
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (unitaryFieldConjugation r f hE)) ≠ 2 := by
    rw [hfixed]
    have hpow := Nat.le_self_pow (show f ≠ 0 by omega) r
    omega
  refine ⟨isometry_all_dimensions_pComponent_quasisimple h hsym hnd hsigma hne hn hq2,
    ?_, ?_⟩
  · intro hsmall
    apply isometry_all_dimensions_small h hsym hnd hsigma hne
    rcases hsmall with hn1 | hnq
    · exact Or.inl hn1
    · exact Or.inr ⟨congrArg Prod.fst hnq, hfixed.trans (congrArg Prod.snd hnq)⟩
  · rintro ⟨hn1, hnq⟩
    have hcases := isometry_all_dimensions_nonsmall h hsym hnd hsigma hne hn hq2 hn1
      (by simpa only [hfixed] using hnq)
    exact ⟨hcases.1, fun p hp L hL => (hcases.2 p hp L hL).1⟩

end CFSG.ComponentClassification.CatalogueBUnitaryTwo
