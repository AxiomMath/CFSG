module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SpTwoPerfectThreeProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

variable {G : Type} [Group G] [Finite G]

theorem agl81TenThreeOneAt_of (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G) (hPar : KFactParabolicPerfectThree) :
    AGL81TenThreeOneAt G := by
  intro hS p P M H Q K hd L hL I₀ hI₀
  rcases hI₀.shape with hc | ⟨_, hb⟩
  · exact three_dvd_card_of_perfect_member hS (hd.toTwoLocalPhaseThree' hS h98) h85 h93
      (noXBlockFor_of_setting hNX3 hS)
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds hPar
      kFactSpTwoPerfectThree_holds
      (fun M S L hK hA hL hX hSy h5 => Or.inr (citedBlockAltSevenPL_holds G M S L hK hA hL hX hSy h5))
      hL hI₀ hc
  · exact three_dvd_card_oUpperTwo_of_symThree hb

end CFSG.LocalAnalysis.RankThreeTheoremC
