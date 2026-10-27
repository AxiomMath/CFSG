module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Data
public import CFSG.LocalAnalysis.AGLEmbedding.A15BlockOrbit
public import CFSG.LocalAnalysis.AGLEmbedding.A15NoBlockOrbit
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree

public section

namespace CFSG.AGLEmbedding

theorem d1CaseThreeA15_closed (hL : KFactA15Local) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hα : KFactThreeOrFiveDvd) (hS : CatalogOuterSolvable)
    (he : KFactBlockFiveNoncyclic) (hf : KFactBlockThreeFives) : D1CaseThreeA15 :=
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  d1CaseThreeA15_of (stmtA15Data_of hL)
    (stmtA15BlockOrbit_of hB3 stmtBlockInnerNormalizer_of h84 h85 h86 hD2 he hf)
    (stmtA15NoBlockOrbit_of hB3 stmtBlockInnerNormalizer_of h84 h86 hD2 hα hS)

end CFSG.AGLEmbedding
