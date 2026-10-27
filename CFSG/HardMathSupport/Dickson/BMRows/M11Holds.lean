module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusB11
public import CFSG.HardMathSupport.Dickson.BMRows.M11Shape

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen11

section Holds


theorem card_centralizer_x11_holds :
    Nat.card (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) = 1045440 :=
  card_centralizer_x11 card_centralizer_eleven_B_le

theorem centElevenBound_holds : CentElevenBound :=
  centElevenBound_of_B card_centralizer_eleven_B_le

end Holds

end CFSG.HardMathSupport.Dickson.BMRows.M11
