module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSpMult
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSpMultON

public section

namespace CFSG.ComponentClassification.GSThmB

theorem sporadicMultTwoPartInput_holds :
    SporadicMultTwoPartInput :=
  ⟨fun Q _ _ hQ he => SpMult.j3_odd_card_center Q hQ he,
    fun Q _ _ hQ he => SpMult.on_odd_card_center Q hQ he⟩

end CFSG.ComponentClassification.GSThmB
