module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.MilestoneLeaves
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.LedgerFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.U33Clause
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Print516
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNCore
import CFSG.CGT.PushingUpLit.K1R.Dispatch
import CFSG.HardMathSupport.Foote.Coordinator.Final
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverFinal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OddCentreE9
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Assembly
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.CoprimeThreeTwoPart
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupL3
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupA5
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupU3
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811CycReduction
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerCentralized
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerSylowFinal
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.InvariantTwoInCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerAutImageFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.TwoLocalSylow

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

theorem d2L34BetaMSideNonConstrainedInput_of_frontier
    (hcore : AGL81II1320Core) (h811 : AGL81I811Cyc) (hD2 : D1NoXBlock) :
    D2L34BetaMSideNonConstrainedInput := by
  have hFF := CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.citedFFL34BestOffender
  have hN : D2L34BetaNormalizerSolvable :=
    d2L34BetaNormalizerSolvable_of_cyclic CFSG.AGLEmbedding.kFactCatalogSchreier
      (Tits.MsidePrelim.d2L34BetaPushUpCoverSyl hFF)
      (d2L34BetaTwoLocalSylowCyclic_of_I811Cyc hFF h811)
  have hC : D2L34BetaLayerCentralized := d2L34BetaLayerCentralized_of_ff hFF kFactRankTwoE9
  exact nonConstrainedInput_of_structure (d2L34BetaLayerExists_of_core hcore hFF hN hD2) hC
    (d2L34BetaLayerPermutable_of_sylow_aut
      (d2L34BetaLayerSylow_of_core Tits.S3AmalgamBound.d2L34BetaInvariantTwoInCore hC)
      (Tits.S3AmalgamBound.d2L34BetaLayerAutImage_proved hN hD2))

theorem lc_gl_embedding_theorem_d2_rank_four_of_frontier
    (hD1 : ∀ (G : Type) [Group G] [Finite G], CFSG.AGLEmbedding.D1Global G → D1For G)
    (hLowN : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLowN)
    (h93 : Asc81bNineThree)
    (hA8 : CFSG.CGT.T75P.A8SylowInput)
    (hNA : CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainNonAbelian)
    (hGLSPlus : Gls3StronglyThreeEmbeddedPlus)
    (h516 : GN.AGL81I516)
    (hFFT : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hR : GN.GNAltSevenThreeRank)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hQH : Q ≤ H) : H ≤ M := by
  obtain ⟨hT2, hT25⟩ := aschbacherTwoK_solomonK_of_remaining hA8 hNA
  have hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK :=
    CFSG.CGT.PushingUpLit.ThmOne.aschbacherTheoremOneK_of_inputs
      CFSG.CGT.PushingUpLit.K1R.stdKernelTwo_holds
      CFSG.HardMathSupport.Foote.Coordinator.endFoote_holds
      CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.stellmacherSixOneThree_holds
  have hD2 : D1NoXBlock := CFSG.AGLEmbedding.d1NoXBlock_of_inputsK hT1 hT2 hT25
  have hGN : McLaughlin.WeakBlockModuleData.GlaubermanNilesInput :=
    GN.glaubermanNiles_of_print_cited h516 hFFT hR
  have hS3 : D2PairStrongThree :=
    McLaughlin.d2PairStrongThree_of_citedInputs h93 hD2 hGLSPlus hGN
      (McLaughlin.FiveThreeAlt.agl81FiveThreeRest_of_u33
        McLaughlin.FiveThreeAlt.agl81FiveThreeU33_proved)
  have h56 : AGL81I56 :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.agl81I56_of_gf2EightFive'
      (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
        CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)
  have hcore : AGL81II1320Core :=
    agl81II1320Core_of_gn' hGN hFFT h56 Tits.S3AmalgamBound.kFactParabolicCoverRankTwo
      Tits.S3AmalgamBound.kFactOddCentreE9
  have h811 : AGL81I811Cyc :=
    I811.agl81I811Cyc_of_kfacts CFSG.AGLEmbedding.kFactCatalogSchreier
      Tits.S3AmalgamBound.CoprimeTwo.kFactCoprimeThreeTwoPart
      (I811.kFactThreeRankOneOvergroup_of_families
        Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple I811.kFactOvergroupL2
        I811.kFactOvergroupL3 I811.kFactOvergroupU3 I811.kFactOvergroupJ1 I811.kFactOvergroupA5)
  exact lc_gl_embedding_theorem_d2_rank_four_of_d1 hD1 hLowN h93 hA8 hNA hS3
    (d2L34BetaMSideNonConstrainedInput_of_frontier hcore h811 hD2) G hnonab hK hchar he hδ₁ hδ₂ p
    hp P M hM hPM Q hQ hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
