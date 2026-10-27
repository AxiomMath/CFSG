module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdONan
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSplit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatHolds
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzCheck

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)

theorem l34ONanStandardExclusion_holds
    (hCI : GSLit.ClassicalInvolutionInput) : L34ONanStandardExclusion :=
  fun _ _ _ hG _ _ hb hJb _ hτ hst hO =>
    false_of_onan_standard hCI l34CyclicProperFixedCatalog_holds GSThmB.cf24CenterGe
      RankTwoSporadic.Suz.suzMultiplierSix hG hb hJb hτ hst hO

end CFSG.ComponentClassification.GrSLit.L34Sec5S
