module

public import CFSG.Yardstones.M1442643da6f2.Definitions
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentralizerFieldsA6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A7
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Main
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddFinal
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC


theorem catalogueCentralizerFacts_of_ds81Even (he : DS81.DS81EvenLie) :
    CFSG.Yardstones.M1442643da6f2.CatalogueCentralizerFacts where
  catZ2A6 := catZ2A6_holds
  catZ2A7 := catZ2A7_holds
  catM10 := catM10_holds
  catE16 := catE16_holds
  kgHS3 := KGHS3.kgHS3_holds
  kgA6Sq := kgA6Sq_holds
  ds81Lemma210Two := DS81.ds81_of_lie DS81.ds81OddLie_holds he

end CFSG.ComponentClassification.CatFC
