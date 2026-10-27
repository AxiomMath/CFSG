module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def Sec7False : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → False

end CFSG.OddStandard.HigherRank.YamadaG23
