module

public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1FrontierOrth
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClHYc
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NoIrrFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.FinalOfTypeBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusFinal

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator

section EightTen

theorem asc81bEightTen_of_residualOutcomes (hR : AlternatingGeometry.EightTenResidualOutcomes) :
    AlternatingGeometry.Asc81bEightTen :=
  have h85 := CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
    CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds
  CFSG.HardMathSupport.Cooperstein.Coordinator.asc81bEightTen_of_printed_large
    (CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.asc81bEightTenPrinted_of_natural
      h85 CFSG.HardMathSupport.Cooperstein.Coordinator.gf2NoFFTripleA7
      (CFSG.HardMathSupport.Cooperstein.Coordinator.eightTenNaturalOnly_of_residual
        (gf2NaturalLSL_of h85 gf2NoFFTripleA7) hR)
      (CFSG.AGLEmbedding.asc81bEightFive_of_factorization
        CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved))
    CFSG.HardMathSupport.Cooperstein.Proving.quadFourExcluded_proved
    (CFSG.HardMathSupport.Cooperstein.Coordinator.eightTwoFourExcludedLarge_of
      CFSG.HardMathSupport.Cooperstein.Proving.eightTwoExcluded_proved
      (gf2NaturalLSL_of h85 gf2NoFFTripleA7))

theorem asc81bEightTen_of_E0_hyc (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    AlternatingGeometry.Asc81bEightTen :=
  asc81bEightTen_of_residualOutcomes (AlternatingGeometry.eightTenResidualOutcomes_of_E0_hyc hE0)

end EightTen

section NineThree

theorem asc81bNineThree_of_frontier_hyc (hE6 : CoopersteinNoIrrFFE6)
    (hTE6 : CoopersteinNoIrrFFTwistedE6) (hLp : LieInput.OrthPlusLeviOb)
    (hLm : LieInput.OrthMinusLeviOb) (hCm : LieInput.OrthMinusCentOb)
    (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    CFSG.AGLEmbedding.Asc81bNineThree :=
  asc81bNineThree_of_frontier_orth hE6 hTE6 hLp hLm hCm
    (AlternatingGeometry.e0NonShortNotHYzStatement_of_hyc hE0)

theorem asc81bNineThree_of_frontier_minus (hE6 : CoopersteinNoIrrFFE6)
    (hTE6 : CoopersteinNoIrrFFTwistedE6) (hLm : LieInput.OrthMinusLeviOb)
    (hCm : LieInput.OrthMinusCentOb) (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    CFSG.AGLEmbedding.Asc81bNineThree :=
  asc81bNineThree_of_frontier_hyc hE6 hTE6 LieInput.orthPlusLeviOb hLm hCm hE0

theorem d1EightTenNineThree_of_open (hE6 : CoopersteinNoIrrFFE6)
    (hTE6 : CoopersteinNoIrrFFTwistedE6) (hLm : LieInput.OrthMinusLeviOb)
    (hCm : LieInput.OrthMinusCentOb) (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    AlternatingGeometry.Asc81bEightTen ∧ CFSG.AGLEmbedding.Asc81bNineThree :=
  ⟨asc81bEightTen_of_E0_hyc hE0, asc81bNineThree_of_frontier_minus hE6 hTE6 hLm hCm hE0⟩

theorem d1EightTenNineThree_of_rest (hTE6 : CoopersteinNoIrrFFTwistedE6)
    (hLm : LieInput.OrthMinusLeviOb) (hCm : LieInput.OrthMinusCentOb)
    (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    AlternatingGeometry.Asc81bEightTen ∧ CFSG.AGLEmbedding.Asc81bNineThree :=
  d1EightTenNineThree_of_open CurtisE6.coopersteinNoIrrFFE6 hTE6 hLm hCm hE0

theorem d1EightTenNineThree_of_three
    (hT : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      TwE6.TwTypeBoundStmt hf K hK σ hσ)
    (hCm : LieInput.OrthMinusCentOb) (hE0 : AlternatingGeometry.E0NonShortNotHYcStatement) :
    AlternatingGeometry.Asc81bEightTen ∧ CFSG.AGLEmbedding.Asc81bNineThree :=
  d1EightTenNineThree_of_rest (TwE6.coopersteinNoIrrFFTwistedE6_of_typeBound hT)
    LieInput.orthMinusLeviOb hCm hE0

end NineThree

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
