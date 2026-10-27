module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverMain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParFinal

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

set_option linter.unusedSectionVars false


theorem agl81I516SymOver_holds : AGL81I516SymOver :=
  agl81I516SymOver_of_kFact
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.kFactChevMinParabolic_proved

end CFSG.AGLEmbeddingD2.Tits.GN516
