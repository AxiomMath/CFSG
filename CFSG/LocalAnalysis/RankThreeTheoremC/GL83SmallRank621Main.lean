module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Core
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem prop614Core23_holds (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactLemma2813) : GL83SmallRankProp614Core23 G := by
  intro P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hvi hex
  obtain ⟨K, b, hK', hb, hSK, hSi, -, R, hSR, hRX, hR2, hRi, hC⟩ := hex
  obtain ⟨f, hD⟩ := exists_data620 hS hsit hsolv hx hz hext hHN hmax hOS hS1 hS2 hvi h3 hK' hb hSK
    hSi
  obtain ⟨e⟩ := he
  exact hD.false_of_campbellFails hS hU0 hD2 hK hsit hsolv e hx hz rfl
    (hext.pair.isMax.1.1.trans inf_le_right) hSR hRX hR2 hRi hC

theorem prop614_of_k_facts (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactBlockFactorThreePrime) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (hK1 : KFactRankTwoUniqueness)
    (hK2 : KFactRankThreeStructure) (h627 : GL83SmallRankProp627 G)
    (h632 : GL83SmallRankProp632 G) (hCamp : KFactCampbell) (hK13 : KFactLemma2813) :
    GL83SmallRankProp614 G :=
  prop614_of_core23 hS hU0 hD2 hK hKF1 hKF2 hK1 hK2 h627 h632 hCamp
    (prop614Core23_holds hS hU0 hD2 hK13)

end CFSG.LocalAnalysis.RankThreeTheoremC
