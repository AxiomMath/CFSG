module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Main
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UFacts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UChief
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMain
public import CFSG.HardMathSupport.U4FF.FromDichotomy

public section

namespace CFSG.Yardstones.M9cbf837c48cf

open CFSG.LocalAnalysis.RankThreeUC

theorem agl81TheoremDSection16_of_ffNatural (hC : U4FFNatural) (hOf : O6ModuleFacts)
    (hOc : O6ChiefFacts) : AGL81TheoremDSection16Statement :=
  agl81TheoremDSection16_of_facts (kFactAGL81I54U4_of_ffNatural hC) u4ModuleFacts u4ChiefFacts hOf hOc

theorem agl81TheoremDSection16_of_dichotomy (hD : CFSG.HardMathSupport.U4FF.U4RankDichotomy)
    (hOf : O6ModuleFacts) (hOc : O6ChiefFacts) : AGL81TheoremDSection16Statement :=
  agl81TheoremDSection16_of_ffNatural (CFSG.HardMathSupport.U4FF.u4FFNatural_of_dichotomy hD) hOf hOc

end CFSG.Yardstones.M9cbf837c48cf
