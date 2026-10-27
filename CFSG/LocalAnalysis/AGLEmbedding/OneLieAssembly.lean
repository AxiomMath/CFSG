module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSide
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTheoremZ
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJChoice

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1CaseOneLieBigAt_of {G : Type} [Group G] [Finite G] (hcc : D1ConstrainedCaseAt G)
    (h1s : D1CaseOneSmallAt G) (h2 : D1CaseTwoAt G) (h3 : D1CaseThreeAt G) (hK : KFactOneLie)
    (hT : KFactOneLieTorus) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (h84 : Asc81bEightFour) (hM : D1OneLieMSide) (hZ : D1OneLieResidue) : D1CaseOneLieBigAt G := by
  intro p P M H R Rbar K hd
  obtain ⟨P₀, H₀, R₀, Rbar₀, K₀, hd₀, huniq⟩ := exists_uniqueOverJ hcc h1s h2 h3 hK hT hd
  exact hd₀.false_of_unique hK h84 hCGT hD2 hZ huniq
    (hM G p P₀ M H₀ R₀ Rbar₀ K₀ hd₀ (huniq.toUniqueOver hd₀.cfg.ext.isPGroup))

theorem d1CaseOneLieBig_of (hβ : KFactBeta) (hα : KFactAlphaW) (h1s : D1CaseOneSmall)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (h84 : Asc81bEightFour)
    (hM : D1OneLieMSide) (hZ : D1OneLieResidue) : D1CaseOneLieBig :=
  fun _ _ _ h4 => d1CaseOneLieBigAt_of ((d1ConstrainedCase_of_kFactsW hβ hα).toAt h4)
    (h1s.toAt h4) (h2.toAt h4) (h3.toAt h4) hK hT hCGT hD2 h84 hM hZ

theorem d1CaseOneLie_of (hβ : KFactBeta) (hα : KFactAlphaW) (h1s : D1CaseOneSmall)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (h84 : Asc81bEightFour)
    (hMC : D1OneLieMSideCore) (hZ : D1OneLieResidue) : D1CaseOneLie :=
  d1CaseOneLie_of_big h1s (d1CaseOneLieBig_of hβ hα h1s h2 h3 hK hT hCGT hD2 h84
    (d1OneLieMSide_of_core hK h84 hD2 hMC) hZ)

end CFSG.AGLEmbedding
