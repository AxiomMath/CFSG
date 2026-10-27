module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154AmbU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin (linLabelDict_holds)


theorem l154FldOn_lin : L154FldOn l154Lin :=
  l154FldOn_of_omega (l154OmegaFld_lin linLabelDict_holds)

theorem l154NIDOn_lin : L154NIDOn l154Lin :=
  l154NIDOn_of_fldOn l154FldOn_lin

theorem l154TD4On_lin : L154TD4On l154Lin :=
  l154TD4On_of_fldOn l154FldOn_lin

theorem l154NonInnDiag_of_rest (hUni : L154NIDOn l154Uni) (hSymp : L154NIDOn l154Symp)
    (hOrth : L154NIDOn l154Orth) (hTwOrth : L154NIDOn l154TwOrth) (hExc : L154NIDOn l154Exc) :
    L154NonInnDiag :=
  l154NonInnDiag_of_families l154NIDOn_lin hUni hSymp hOrth hTwOrth hExc l154NIDOn_ambAlt
    l154NIDOn_ambU33

theorem l154NotTD4_of_rest (hUni : L154TD4On l154Uni) (hSymp : L154TD4On l154Symp)
    (hOrth : L154TD4On l154Orth) (hTwOrth : L154TD4On l154TwOrth) (hExc : L154TD4On l154Exc) :
    L154NotTD4 :=
  l154NotTD4_of_families l154TD4On_lin hUni hSymp hOrth hTwOrth hExc l154TD4On_ambAlt
    l154TD4On_ambU33

end CFSG.LocalAnalysis.GLTheoremA.K155X
