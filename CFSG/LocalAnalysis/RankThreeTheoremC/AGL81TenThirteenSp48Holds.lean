module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSp48
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Holds
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48NSLoc
import CFSG.LocalAnalysis.RankThreeTheoremC.BlockL28TransvectionProof
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable (G : Type) [Group G] [Finite G]


theorem agl81TenThirteenSp48_holds_of_sigma (hσ : 3 ∈ rankThreeSigmaA G)
    (h93 : Asc81bNineThree) (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G) :
    Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ I₀ ∈ cZero (H ⊓ L), IsTwoPrimeComponent I₀ I₀ →
      ∀ (q : TauCeti.PrimePower) (dK dJ : TauCeti.ValidLieTypeIndex), q.p = 2 →
      q.exponent = 3 → dK.1 = .B 2 q → dJ.1 = .A 1 q → Nonempty (K ≃* CatGroup dK) →
      ∀ f : I₀ →* CatGroup dJ, Function.Surjective f →
        (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker → False :=
  agl81TenThirteenSp48_of_sigma G hσ kFactSp48NonsolvLocal
    (kFactBlockL28Transvection_of_pl
      (citedBlockTransvectionPL_of_type
        CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds)
      kFactSpTwoSimple_holds)
    KFactProofs.kFactBlockL28Rank_holds KFactProofs.kFactBlockL28TwoRank_holds
    (asc81bEightFive_of_factorization aschbacherLocalFactorization_proved) h93 hNX
    Hyp111.agl81NineEightFour_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
