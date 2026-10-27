module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PrimeBlocksD2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ComponentsK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2MSideCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

theorem d2L2MSide3_of (hX : D1NoXBlock3 G) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) : D2L2MSide3 G := by
  intro hS hD1 M hM ha hb p _ hp hp5 P A H hMP hesc hmax Rbar K hRbar hK ⟨e⟩
  have hglob := aglGlobal_of_setting hS
  have hD1G : D1For G := d1For_of_setting hS
  have hD2 := noXBlockFor_of_setting hX hS
  have hdata := hesc.l2Data_of_psl2 hglob hRbar hK e
  exact hdata.pCore_ne_bot_of_components hD1G hp5 h84 hD2
    (fun L hL hLK => hesc.barM_le_centralizer_of_le_inf hglob hRbar hK e hD1G hp5 hα hSch hL hLK)
    (fun L hL => hdata.barM_le_centralizer_of_weakSBlock hD1G h84 h85 h86 h93 hD2 hK2 hC3 hK5
      hKin hKP hC3p hK5p hp5 hL)

end CFSG.LocalAnalysis.RankThreeTheoremC
