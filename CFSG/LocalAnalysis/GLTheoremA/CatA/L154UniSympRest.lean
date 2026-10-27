module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X


theorem l154NonInnDiag_of_rest_uni_symp (hOrth : L154NIDOn l154Orth) (hTwOrth : L154NIDOn l154TwOrth)
    (hExc : L154NIDOn l154ExcRest) : L154NonInnDiag :=
  l154NonInnDiag_of_rest_uni CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154NIDOn_symp hOrth hTwOrth hExc

theorem l154NotTD4_of_rest_uni_symp (hOrth : L154TD4On l154Orth) (hTwOrth : L154TD4On l154TwOrth)
    (hExc : L154TD4On l154ExcRest) : L154NotTD4 :=
  l154NotTD4_of_rest_uni CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154TD4On_symp hOrth hTwOrth hExc

end CFSG.LocalAnalysis.GLTheoremA.K155X
