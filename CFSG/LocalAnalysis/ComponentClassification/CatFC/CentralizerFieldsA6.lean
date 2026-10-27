module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SmallHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC


theorem catZ2A6_holds : CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)) :=
  catZ2A6_of_small a6InnerLieSmall_holds a6OuterLieSmall_holds

theorem catM10_holds : CFSG.EvenSporadicStandard.CatM10AlmostSimple :=
  catM10_of_arms a6InnerLieSmall_holds a6OuterLieSmall_holds catZ2A6_holds

end CFSG.ComponentClassification.CatFC
