module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExF4
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExE6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExE7
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExE8
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExG2
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExSz
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTwE6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExD4
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExRee
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTits

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

set_option linter.unusedSectionVars false

theorem lie23To89At_of_nonclassical {t : StatedLieTag} (ht : t ∉ classicalTags) :
    Lie23To89At t := by
  cases t <;> first
    | exact lie23To89At_G2
    | exact lie23To89At_F4
    | exact lie23To89At_E6
    | exact lie23To89At_E7
    | exact lie23To89At_E8
    | exact lie23To89At_twistedE6
    | exact lie23To89At_trialityD4
    | exact lie23To89At_twistedB2
    | exact lie23To89At_twistedG2
    | exact lie23To89At_twistedF4
    | exact lie23To89At_Tits
    | exact absurd (by decide) ht

end CFSG.ComponentClassification.CatFC.DS81.Ex
