module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Assembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GraphOrbitProof
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Main

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

set_option linter.unusedSectionVars false

theorem agl81I516_of_graphOrbit (hG : KFactChevGraphOrbit) (hSym : AGL81I516SymOver) :
    GN.AGL81I516 :=
  agl81I516_of_inputs E23.e23NonsolvGen
      CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.kFactChevMinParabolic_proved
      (natMultiBaumStab_of_graphOrbit hG) kFactChevMinParabolicLevi_proved hSym

end CFSG.AGLEmbeddingD2.Tits.GN516
