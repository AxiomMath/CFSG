module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13D
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278SporCMon13DQ2

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13

open Subgroup CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal

theorem kdI278SporCMonster_holds
    : KDI278SporCMonster :=
  kdI278SporCMonster_of_sl33 sl33_no_normalizer_thirteen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Monster13
