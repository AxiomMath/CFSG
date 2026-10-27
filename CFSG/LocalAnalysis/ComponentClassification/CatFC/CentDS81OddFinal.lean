module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddRee
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddExc
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddExcE7
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddSpMat
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddUniMat
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddOrthFam
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

set_option linter.unusedSectionVars false


theorem ds81OddLie_holds : DS81OddLie :=
  ds81OddLie_of_dichotomy (oddDichotomy_of_families fun t => by
    cases t
    · exact oddDichotomyFamily_PSL
    · exact oddDichotomyFamily_PSU
    · exact oddDichotomyFamily_PSp
    · exact oddDichotomyFamily_POmegaOdd
    · exact oddDichotomyFamily_POmegaPlus
    · exact oddDichotomyFamily_POmegaMinus
    · exact oddDichotomyFamily_G2
    · exact oddDichotomyFamily_F4
    · exact oddDichotomyFamily_E6
    · exact oddDichotomyFamily_E7
    · exact oddDichotomyFamily_E8
    · exact oddDichotomyFamily_twistedE6
    · exact oddDichotomyFamily_trialityD4
    · exact oddDichotomyFamily_twistedB2
    · exact oddDichotomyFamily_twistedG2
    · exact oddDichotomyFamily_twistedF4
    · exact oddDichotomyFamily_Tits)

end CFSG.ComponentClassification.CatFC.DS81
