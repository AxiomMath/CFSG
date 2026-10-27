module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3FineKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceBlocks
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9Local
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanJStarA9
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimFive
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarD4TwoThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanE6TwoRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvClosed
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeF4Target
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp48Target
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Data
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48NSLoc
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62Local
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaEightMinusAut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFive
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSpor
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.LocalAnalysis.AGLEmbedding.POneThreeAlt
import CFSG.LocalAnalysis.AGLEmbedding.JStarElimAlt
import CFSG.LocalAnalysis.AGLEmbedding.JStarElimSpor
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductions
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2
import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuterAux
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62RankFacts
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Milestones.FAM_M_finiteness
import CFSG.Milestones.FAM_M_simplicity
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AltSixSevenAut
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.MonsterDefs
public import CFSG.Open.MonsterY443Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

theorem D1CaseThreeFineKFacts3.of_inputs (hg : D1CaseThreeG28A15Facts) (hL : D2KFactLeaves)
    (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hReeF4 : KFactReeF4Local)
    (hSolv : KFactBlockThreeSolvableBeta)
    (hK3 : CitedBlockTransvectionCyclic) (hK4 : CitedBlockAltNormalizer)
    (hNine : KFactBlockThreeOrderNine) (hLevi : KFactBlockLeviU42)
    (hOneOrbit : KFactBlockThreeOneOrbit)
    (hGL : CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedThreeSolvable)
    (hSp62Frame : KFactSp62Frame) (hOmega8Frame : KFactOmega8Frame)
    (hL28Transvection : KFactBlockL28Transvection) (hL28Rank : KFactBlockL28Rank)
    (hL28TwoRank : KFactBlockL28TwoRank) :
    D1CaseThreeFineKFacts3 := by
  have hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group) :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder :=
    CFSG.Milestones.fam_m_finiteness
  have hMsimple : IsSimpleGroup CFSG.Open.MonsterY443Derived := CFSG.Milestones.fam_m_simplicity
  have hOutS := not_dvd_card_outer_sporadic_of hbr hMsimple
  have hSch : KFactCatalogSchreier := hL.catalogSchreier
  have hKR8 : KFactReeOrder := kFactReeOrder
  have hOR : KFactJ3OuterRank := kFactJ3OuterRank_closed (hbr .J3)
  have hT3 := stmtJ3Target_of (hbr .J3) hOR
  have hLBRc := stmtLemmaBRelCyc_of_irrPB hL.nineThree
    CFSG.AGLEmbedding.ParabAutIrr.kFactParabolicAutomizerIrrPB kFactAltSixSevenAut hK3 hK4
  exact
    { toD1CaseThreeG28A15Facts := hg
      beta := hβ
      p1Lie := hP1L
      p1Alt := kFactP1ThreeAlt
      p1Spor := kFactP1ThreeSpor_of hbr hOutS hMcard
      localCGT := hL.localCGT
      reeF4Local := hReeF4
      reeF4Target := stmtReeF4Target
      jStarElimReeF4 := kFactJStarElimReeF4_of hSch hbr hMcard
      blockFiveParabolic :=
        kFactBlockFiveParabolic_of hL.parabolicPrime hL.citedBlockPrime hL.blockAltSevenPrime
      outFiveCyclic := kFactOutFiveCyclic_of_dvd kFactOutElemRankOdd kFactOutFiveCyclicDvd
      j3Sylow := kFactJ3Sylow
      j3OuterInvolution := kFactJ3OuterInvolution
      j3OuterRank := hOR
      j3Target := hT3.1
      j3TargetCard := hT3.2
      jStarElimJ3 := kFactJStarElimJ3_of hSch hKR8 hbr hMcard
      blockThreeSolvable := kFactBlockThreeSolvable_of_beta hSolv hg.blockThreeOut hg.nineThree
      jStarElimLie := kFactJStarElimLie_of_e6_residual hSch hKR8 jStarResidualE6TwoSix
      jStarElimAlt := kFactJStarElimAlt
      jStarElimSpor := kFactJStarElimSpor_of hbr hOutS hMcard hMsimple
      lemmaB := stmtLemmaB_of_rel (stmtLemmaBRel_of_cyc hLBRc)
      outElemRank := kFactOutElemRank_of_odd kFactOutElemRankOdd
      sp48Local := kFactSp48Local
      sp48Data := kFactSp48Data
      sp48NonsolvLocal := kFactSp48NonsolvLocal
      sp48Target := stmtSp48Target
      jStarElimSp48 := kFactJStarElimSp48_of hSch hKR8 hbr hMcard
      blockThreeOrderNine := hNine
      blockL28Transvection := hL28Transvection
      blockL28Rank := hL28Rank
      blockL28TwoRank := hL28TwoRank
      sp62Local := kFactSp62Local
      blockLeviU42 := hLevi
      omegaEightMinusAut := kFactOmegaEightMinusAut
      u62ThreeRank := kFactU62ThreeRank
      omegaMinusThreeRank := kFactOmegaMinusThreeRank
      gl83 := hGL
      sp62Frame := hSp62Frame
      omega8Frame := hOmega8Frame
      a9Local := kFactA9Local
      jStarElimA3p := kFactJStarElimA3p_three hSch hKR8 hbr hMcard
      blockThreeOneOrbit := hOneOrbit }

end CFSG.LocalAnalysis.RankThreeTheoremC
