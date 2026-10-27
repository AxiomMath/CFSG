module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMReduction

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit

@[expose] def LocalBalanceCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X → LocallyTwoBalanced X

@[expose] def HeldCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X → ¬ OutcomeLocal.UOutcome X → LocallyTwoBalanced X →
    ¬ ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ L ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)

@[expose] def L34Case : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X → LocallyTwoBalanced X →
    (¬ ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ L ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)) →
    ¬ ∃ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L ∧
      Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2

theorem grslit_of_cases (hLB : LocalBalanceCase) (hHe : HeldCase) (hL34 : L34Case) :
    GriessSolomonInput := by
  rintro X _ _ _ hnonab hK hz hU ⟨x, y, L, hT, htype⟩
  have hloc := hLB X hnonab hK hz hU
  have hnoHe := hHe X hnonab hK hU hloc
  rcases htype with hHeL | h34
  · exact hnoHe ⟨x, L, hT.1, hT.2.2.2.1, hT.2.2.2.2.1, hHeL⟩
  · exact hL34 X hnonab hK hz hU hloc hnoHe ⟨x, y, L, hT, h34⟩

@[expose] def HeldMaximalCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ¬ ∃ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J ∧
      (∀ (c v : X) (K : Subgroup X), GSUnbalancingTriple c v K →
        (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) ∧
      Nonempty (J ⧸ pPrimeCore 2 J ≃* Blueprint.NativeSporadic.He)

@[expose] def L34MaximalCase : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ¬ ∃ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J ∧
      (∀ (c v : X) (K : Subgroup X), GSUnbalancingTriple c v K →
        (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) ∧
      Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2 ∧ GSMaximalComponent J

theorem grslit_of_maximal_cases
    (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGF : GloballyFirstRankTwoInput) (hB : TheoremBBoundedInput) (hH : HarrisInput)
    (hF : FooteLit.FooteMaximalInput) (hHSF : HarrisSolomonFritzInput)
    (hCI : ClassicalInvolutionInput) (hHe : HeldMaximalCase) (hL34 : L34MaximalCase) :
    GriessSolomonInput := by
  rintro X _ _ _ hnonab hK hz hU ⟨x, y, L, hT, -⟩
  obtain ⟨a, x', J, hJ, hbound, hHeJ | ⟨h34, hmax⟩⟩ :=
    GSFM.exists_maximal_he_or_l34 hTB hSA hGF hB hH hF hHSF hCI X hnonab hK hz hU
      ⟨x, y, L, hT⟩
  · exact hHe X hnonab hK hz hU ⟨a, x', J, hJ, hbound, hHeJ⟩
  · exact hL34 X hnonab hK hz hU ⟨a, x', J, hJ, hbound, h34, hmax.gsMaximalComponent⟩

theorem heldMaximalCase_of_cases (hLB : LocalBalanceCase) (hHe : HeldCase) :
    HeldMaximalCase := by
  rintro X _ _ _ hnonab hK hz hU ⟨a, x, J, hJ, -, hHeJ⟩
  exact hHe X hnonab hK hU (hLB X hnonab hK hz hU)
    ⟨a, J, hJ.1.1, hJ.1.2.2.2.1, hJ.1.2.2.2.2.1, hHeJ⟩

theorem l34MaximalCase_of_cases (hLB : LocalBalanceCase) (hHe : HeldCase) (hL34 : L34Case) :
    L34MaximalCase := by
  rintro X _ _ _ hnonab hK hz hU ⟨a, x, J, hJ, -, h34, -⟩
  have hloc := hLB X hnonab hK hz hU
  exact hL34 X hnonab hK hz hU hloc (hHe X hnonab hK hU hloc) ⟨a, x, J, hJ.1, h34⟩

end CFSG.ComponentClassification.GrSLit
