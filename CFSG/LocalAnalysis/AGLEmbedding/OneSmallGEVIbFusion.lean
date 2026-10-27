module

import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem false_of_d1LiftX_le_C (hc : D1IbConfig p P M H R Rbar K z) (hOrb : KFactSmallOrbits)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hTC : d1LiftX p H R K ≤
      rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) : False :=
  hc.toZCore.false_of_d1LiftX_le_C hOrb hL hBL hzbL (hc.zbar_not_mem_centralizer hL) hTC

end D1IbConfig

end CFSG.AGLEmbedding
