module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltM4
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltCaseA

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.ComponentClassification

theorem end4Alt_of_caseA_inputs (hB : TauCetiCatalogBridge)
    (hK3 : RankTwoStandard.RankTwoAlternatingStandard) (hNL : NatLiftStatement)
    (hA : AltCaseA) : End4Alt :=
  end4Alt_of_caseA hNL (alt2Rank1_holds hB hK3 hNL) hA

end CFSG.CGT.PushingUpLit.CGT6
