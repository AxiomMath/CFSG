module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154UniSympRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K155XRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

section ExcOnly


theorem i155XRes_of_excRest (hN : L154NIDOn l154ExcRest) (hT : L154TD4On l154ExcRest) : I155XRes :=
  ⟨l154NonInnDiag_of_rest_uni_symp K155XOr.l154NIDOn_orth K155XOr.l154NIDOn_twOrth hN,
    l154NotTD4_of_rest_uni_symp K155XOr.l154TD4On_orth K155XOr.l154TD4On_twOrth hT⟩

end ExcOnly

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
