module

public import CFSG.HardMathSupport.Foote.Coordinator.Assembly
public import CFSG.HardMathSupport.Foote.Coordinator.Sporadic
public import CFSG.HardMathSupport.Foote.Coordinator.SporadicJ1
public import CFSG.HardMathSupport.Foote.Coordinator.SporadicModels
public import CFSG.HardMathSupport.Foote.Coordinator.ExcFive
public import CFSG.HardMathSupport.Foote.FamilyReduction.Targets
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.Mult.Exceptional

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.CGT.PushingUpLit.CGT6

set_option linter.unusedSectionVars false

section ExcFive


theorem excFiveTarget : ExcFiveTarget :=
  excFiveTarget_of_exceptionalCenterSmallPrimes
    (RankThree.PartOne.Mult.exceptionalCenterSmallPrimes_of_griess
      FamilyReduction.griessAllModelsStatement)

end ExcFive

section EndFoote


theorem endFoote_holds : EndFoote :=
  endFoote_of_targets RankThree.PartOne.TCB.tauCetiCatalogBridge FamilyReduction.altTarget
    (open CFSG.Blueprint in sporTarget_of_four (end415K_J1 (MulEquiv.refl _))
        (end415K_J2 (MulEquiv.refl _)) (end415K_J3 (MulEquiv.refl _))
        (end415K_M12 (MulEquiv.refl _))) FamilyReduction.classicalOffFiveTarget FamilyReduction.excOffFiveTarget
    FamilyReduction.reeTitsSuzukiTarget FamilyReduction.classicalFiveTarget excFiveTarget

end EndFoote

end CFSG.HardMathSupport.Foote.Coordinator
