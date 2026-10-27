module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Five

public section

namespace CFSG.EvenSporadicStandard.HSStd

open CFSG.EvenSporadicStandard.Induction

theorem hsSection5_of_steps'
    (hr : NoA8.HSInnerRest) (hgood : HSOuterGoodCase) (hL44 : HSOuterL44Free)
    (hsw : HSOuterSwapFree) (hH : Harada39One) (hI : HaradaFourInspection)
    (hY : NoA8.HSOuterFiveYStep) (hP13 : NoA8.HSMinCexProp13) (hL21 : NoA8.HSMinCexLemma21)
    (hCat : CatNoOuterHS) : HSSection5Hered :=
  NoA8.hsSection5_of_fiveCase hr hgood hL44 hsw (NoA8.hsOuterFiveCase_of_steps hs100Model hH hI hY)
    hP13 hL21 hCat

end CFSG.EvenSporadicStandard.HSStd
