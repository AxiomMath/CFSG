module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
public import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveCtxCZero
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveCtxASeven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockOrderThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockRankTable
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabPerfectThreeHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SpTwoPerfectThreeProof
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


theorem twelveFourBlockFacts_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (h93 : Asc81bNineThree)
    (hN1 : CFSG.LocalAnalysis.AGL81I.Section4.AGL81FourNineteen)
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H) :
    TwelveFourBlockFacts M H L where
  three_dvd := three_dvd_card_inf_of_mem_weakBlockSet h1 h2 h25 h hL
  cZero_nonempty := cZero_inf_nonempty_of_twelveCtx h1 h2 h25 h93
    (RankThreeTheoremC.ParabCensus.kFactParabolicLeviMember_of_griess
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement) h hL
  three_dvd_oUpperTwo _ hI := three_dvd_card_oUpperTwo_of_twelveCtx h1 h2 h25 h93
    RankThreeTheoremC.kFactParabolicPerfectThree_holds
    RankThreeTheoremC.kFactSpTwoPerfectThree_holds h hL hI
  aSeven_primes h5 _ hr hrd :=
    eq_two_or_three_of_prime_dvd_card_inf_of_twelveCtx h1 h2 h25 h hL h5 hr hrd
  order_three := exists_orderOf_three_not_mem_centralizer_barM h1 h2 h25 h hL
  rank_table h3L _ hd hd5 hdL :=
    pRank_barM_add_one_le_of_mem_weakBlockSet h1 h2 h25 hN1 h hL h3L hd hd5 hdL

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
