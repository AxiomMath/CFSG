module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Main
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAFromMain
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseBFinal

public section

namespace CFSG.OddStandard.Seitz77

section Proved


theorem seitz77SimpleL34_of_gh74 (hGH : ComponentClassification.UFrontier.GH74ModelsInput) :
    Seitz77SimpleL34 :=
  seitz77SimpleL34_of_cases hGH seitz77CaseAFalse seitz77CaseBFalse

end Proved

end CFSG.OddStandard.Seitz77
