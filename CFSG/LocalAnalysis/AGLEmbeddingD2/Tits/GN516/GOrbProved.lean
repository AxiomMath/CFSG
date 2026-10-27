module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbFamAll
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbReduce

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

theorem kFactChevGraphOrbit_proved :
    KFactChevGraphOrbit :=
  kFactChevGraphOrbit_of_simple
    (kFactChevGraphOrbitSimple_of_cases fun _ _ _ _ hC => hasBQGraph_or_residualGraph hC)

end CFSG.AGLEmbeddingD2.Tits.GN516
