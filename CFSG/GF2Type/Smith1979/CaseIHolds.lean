module

public import CFSG.GF2Type.Smith1979.CaseI25Main
public import CFSG.GF2Type.Smith1979.IdxFourModelE0Facts
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LargeExtraspecial.S4CEMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

theorem caseIStmt_holds : CaseIStmt :=
  caseIStmt_of_notTwoCentral CFSG.LargeExtraspecial.S4.centralExtInput
    (Case25.caseINotTwoCentral_of_U43 CFSG.LargeExtraspecial.S4.centralExtInput
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
      (Case25.filterXInCatalog_of_bridge CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge)
      Case25.u43NoFaithfulTwelve IdxFour.modelInput_holds IdxFour.card_E0 IdxFour.e0Facts)

end CFSG.GF2Type.Smith1979
