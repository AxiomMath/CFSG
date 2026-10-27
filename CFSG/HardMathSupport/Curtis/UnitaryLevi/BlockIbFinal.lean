module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDispatch
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwistedA
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSp
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbD
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwistedD
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbG2
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSmall
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbAltAssembly
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbA

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique


theorem kFactBlockCentRankIbThree_of_A (hA : BlockIbRankFam (IsLieOf IdxA))
    (h85 : Asc81bEightFive) (hT : CitedBlockTransvectionPLType) :
    KFactBlockCentRankIbThree :=
  kFactBlockCentRankIbThree_of_families hA blockIbRankFam_twistedA blockIbRankFam_b
    blockIbRankFam_d blockIbRankFam_twistedD blockIbRankFam_g2 blockIbRankFam_small
    (blockIbRankRest_of_cited h85 hT)

theorem kFactBlockCentAbThreeIb_of_A (hA : BlockIbAbFam (IsLieOf IdxA))
    (h85 : Asc81bEightFive) (hT : CitedBlockTransvectionPLType) :
    KFactBlockCentAbThreeIb :=
  kFactBlockCentAbThreeIb_of_families hA blockIbAbFam_twistedA blockIbAbFam_b
    blockIbAbFam_d blockIbAbFam_twistedD blockIbAbFam_g2 blockIbAbFam_small
    (blockIbAbRest_of_cited h85 hT)

theorem kFactBlockCentRankIbThree_holds (h85 : Asc81bEightFive)
    (hT : CitedBlockTransvectionPLType) : KFactBlockCentRankIbThree :=
  kFactBlockCentRankIbThree_of_A blockIbRankFam_A h85 hT

theorem kFactBlockCentAbThreeIb_holds (h85 : Asc81bEightFive)
    (hT : CitedBlockTransvectionPLType) : KFactBlockCentAbThreeIb :=
  kFactBlockCentAbThreeIb_of_A blockIbAbFam_A h85 hT

end CFSG.HardMathSupport.Curtis.UnitaryLevi
