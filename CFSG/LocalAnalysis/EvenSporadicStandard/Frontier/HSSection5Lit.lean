module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.HSSection5Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.HNExclusionHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Section5Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.NoHSOddPump
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimple

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Yardstones.M1442643da6f2

theorem hsSection5_of_sol78LitCore
    (h05 : InvolutionCentralizerTheorems) (h06 : ONanInputs) (h11 : HNRecognitionInputs)
    (lit : Induction.Sol78LitCore) (hCIT : Induction.CITPart2) :
    HSStd.HSSection5 :=
  HSStd.hsSection5_of_hered
    CFSG.ComponentClassification.FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
    (hsSection5Hered_of_ctssInputs h05 h06 lit.fs79lemma15 lit.fs79thm13 hCIT
      (Induction.hnStdExclusionHered_of_hnRow lit
        ⟨CFSG.ComponentClassification.CatFC.oddLieCompNotSporadic_holds⟩
        (child7_of_frontier h11.haradaHN
          (TwoHS.GH312.gh312Fixed_of_gh74 fun G _ _ _ hnonab hrank hsect =>
            CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab hrank hsect))
        (Induction.Balance.catalogNoHSOdd_of_kgPumpTableT
          CFSG.ComponentClassification.CatFC.kgPumpTableT_holds)))

end CFSG.EvenSporadicStandard.Frontier
