module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenPair
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Table
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Monster.Generated (Gmat)
open CFSG.Open (monsterOrder)


theorem twoRankLe_thirteen_M : TwoRankLe 13 .M 2 := by
  have hG := CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  haveI : Finite Gmat := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num [monsterOrder])
  have hrk := CFSG.AGLEmbedding.pRank_le_two_of_hasNoncommPair (by norm_num)
    (by rw [hG]; norm_num [monsterOrder])
    CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_thirteen_Gmat
  obtain ⟨b⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact twoRankLe_two_of_bound (by norm_num) ⟨b⟩
    (CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_pRank_le (by norm_num) hrk)

end CFSG.LocalAnalysis.GLTheoremA.H1017
