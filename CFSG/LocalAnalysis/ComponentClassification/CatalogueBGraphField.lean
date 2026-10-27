module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBHigherLinearInner CatalogueBUnitaryTwo

universe u

theorem odd_linear_graph_field_scalar_involution_conjugacy
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (hidentity : scalarGraphFieldAction n K A sigma ≠ 1)
    (hsquare : scalarGraphFieldAction n K A sigma ^ 2 = 1) :
    Even f ∧ (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = p ^ (f / 2) ∧
      ∃ H : GL (Fin n) K, scalarGraphFieldAction n K A sigma =
        scalarInnerDiagonalAction n K H * scalarGraphFieldAut n K sigma *
          (scalarInnerDiagonalAction n K H)⁻¹ := by
  obtain ⟨hidentity', hsquare'⟩ := scalarGraphField_involution_data n K A sigma hidentity hsquare
  obtain ⟨heven, hformula, hfixed, H, hH⟩ := odd_linear_graph_field_involution_conjugacy
    n K p f hp hpodd hf hcard hn A sigma hne hidentity' hsquare'
  refine ⟨heven, hformula, hfixed, H, ?_⟩
  let e := MulAut.congr (scalarProjectiveSpecialLinearEquiv n K)
  apply e.injective
  rw [scalarGraphFieldAction_congr, map_mul, map_mul, map_inv,
    scalarInnerDiagonalAction_congr, scalarGraphFieldAut_congr]
  exact hH

theorem odd_linear_graph_field_involution_fixed_p_components_native
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (_hidentity : graphFieldAction n K A sigma ≠ 1)
    (hsquare : graphFieldAction n K A sigma ^ 2 = 1) :
    Even f ∧ 1 ≤ f / 2 ∧
      ∃ hunitary : Nat.card K = (p ^ (f / 2)) ^ 2,
        unitaryFieldConjugation p (f / 2) hunitary = sigma ∧
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = p ^ (f / 2) ∧
        3 ≤ Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) ∧
        ∀ (ell : ℕ), ell.Prime → ∀ L : Subgroup (twistedFixedPSL n K A sigma),
          CFSG.IsPComponent ell L → CFSG.IsQuasisimple L ∧
            Nonempty (L ≃* UnitaryDataProjectiveSpecial n K p (f / 2) hunitary) := by
  obtain ⟨heven, hhalf, hunitary, hbar, _hformula, hfixed, hnq⟩ :=
    odd_graphField_unitary_data n K p f (Fact.out : p.Prime) hpodd hf hcard hn A sigma hne hsquare
  change unitaryFieldConjugation p (f / 2) hunitary = sigma at hbar
  have hthree : 3 ≤ Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) := by
    rw [hfixed]
    exact odd_prime_power_three_le p (f / 2) Fact.out hpodd hhalf
  refine ⟨heven, hhalf, hunitary, hbar, hfixed, hthree, ?_⟩
  intro ell hell L hL
  have hfull := graphField_involution_fixed_pComponent_projectiveSpecialUnitary
    n K hn A sigma hne hsquare hnq ell hell L hL
  refine ⟨hfull.1, ?_⟩
  change Nonempty (L ≃* ProjectiveSpecialUnitary n K (unitaryFieldConjugation p (f / 2) hunitary))
  rw [hbar]
  exact hfull.2

theorem odd_linear_graph_field_involution_fixed_p_components
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (hidentity : scalarGraphFieldAction n K A sigma ≠ 1)
    (hsquare : scalarGraphFieldAction n K A sigma ^ 2 = 1) :
    Even f ∧ 1 ≤ f / 2 ∧
      ∃ hunitary : Nat.card K = (p ^ (f / 2)) ^ 2,
        unitaryFieldConjugation p (f / 2) hunitary = sigma ∧
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = p ^ (f / 2) ∧
        3 ≤ Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) ∧
        ∀ (ell : ℕ), ell.Prime →
          ∀ L : Subgroup (TauCeti.fixedSubgroup (scalarGraphFieldAction n K A sigma).toMonoidHom),
            CFSG.IsPComponent ell L → CFSG.IsQuasisimple L ∧
              Nonempty (L ≃* UnitaryDataProjectiveSpecial n K p (f / 2) hunitary) := by
  obtain ⟨hidentity', hsquare'⟩ := scalarGraphField_involution_data n K A sigma hidentity hsquare
  obtain ⟨heven, hhalf, hunitary, hbar, hfixed, hthree, hfull⟩ :=
    odd_linear_graph_field_involution_fixed_p_components_native
      n K p f hpodd hf hcard hn A sigma hne hidentity' hsquare'
  refine ⟨heven, hhalf, hunitary, hbar, hfixed, hthree, ?_⟩
  intro ell hell L hL
  let e := scalarGraphFieldFixedEquiv n K A sigma
  let M := L.map e.toMonoidHom
  have hM : CFSG.IsPComponent ell M := CatalogueBAlternating.pComponent_map_equiv ell e L hL
  obtain ⟨hMquasi, ⟨eM⟩⟩ := hfull ell hell M hM
  let eL := L.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv eL (CatalogueBAlternating.quasisimple_iff_native.mp hMquasi)),
    ⟨eL.trans eM⟩⟩

end

end CFSG.ComponentClassification.CatalogueBGraphField
