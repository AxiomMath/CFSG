module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKill
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFrontierFinal

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

theorem rankTwoStdRec_proved
    : RankTwoStdRec :=
  fun G _ _ _ hnonab hK L hL hrank =>
    CFSG.ComponentClassification.RankTwoStandard.ct_rank_two_standard_recognition_models G hnonab
      hK L hL hrank

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
