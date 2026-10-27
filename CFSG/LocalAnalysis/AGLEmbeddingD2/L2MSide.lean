module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2MSideCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ComponentsK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlocksD2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Case

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem d2L2MSide_of (hα : KFactThreeOrFiveDvd) (hSch : KFactCatalogSchreier)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hBC : D2BlocksCentralized) : D2L2MSide := by
  intro G _ _ hglob hD1 p _ hp5 P M A H hesc _ _ Rbar K hRbar hK ⟨e⟩
  have hdata := hesc.l2Data_of_psl2 hglob.toAGLGlobal hRbar hK e
  exact hdata.pCore_ne_bot_of_components hD1 hp5 h84 (hD2.noXBlockFor hglob.toD1Global)
    (fun L hL hLK => hesc.barM_le_centralizer_of_le_inf hglob.toAGLGlobal hRbar hK e hD1 hp5 hα
      hSch hL hLK)
    (fun L hL => hBC G hglob hD1 p M H A A hdata hp5 L hL)

end CFSG.AGLEmbeddingD2
