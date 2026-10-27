module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Uni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X


theorem l154NonInnDiag_of_rest_uni (hSymp : L154NIDOn l154Symp) (hOrth : L154NIDOn l154Orth)
    (hTwOrth : L154NIDOn l154TwOrth) (hExc : L154NIDOn l154ExcRest) : L154NonInnDiag :=
  l154NonInnDiag_of_rest_exc l154NIDOn_uni hSymp hOrth hTwOrth hExc

theorem l154NotTD4_of_rest_uni (hSymp : L154TD4On l154Symp) (hOrth : L154TD4On l154Orth)
    (hTwOrth : L154TD4On l154TwOrth) (hExc : L154TD4On l154ExcRest) : L154NotTD4 :=
  l154NotTD4_of_rest_exc l154TD4On_uni hSymp hOrth hTwOrth hExc

end CFSG.LocalAnalysis.GLTheoremA.K155X
