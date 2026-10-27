module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenOne
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixMoreoverProof
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralHolds
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Holds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNormalComplementHolds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Main
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneFi22GenHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixInputOfMoreover
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeFiveA11InputHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.TwelveElevenNineSeven
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenTwoGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CReduction
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Co3Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveRed
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ONThree
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo3
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporRed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Normalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.ON
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzRowAtlas
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Ambiguous
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.L2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.CentralizerK
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.N143.SecRankHard
public import CFSG.RankThree.PartOne.S10.PlaneLocalRankContract
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools
public import Certificates.Certificate12623
public import Certificates.Certificate19800
public import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem nineNineOneInput_of_o991Gen (h991 : O991Gen) (h971 : NineSevenOneGen) :
    NineNineOneInput := by
  intro G _ _ M Q H E p hn hpσ
  obtain ⟨hp, hp2, -⟩ := mem_QSet_iff.mp hn.mem_Q
  by_cases hp3 : p = 3
  · subst hp3
    intro A hAM hA hAc hAΓ
    exact h991 G hn.setting.cstar M hn.setting.maxLocal hn.setting.sigma_nonempty hpσ A hAM hA
      (by rw [hAc]; norm_num) hAΓ
  · exact nineNineOne_of_nineSevenOneAt hn.setting h971.nineSevenOneAt hp
      (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hpσ

section


theorem o991Gen_holds : O991Gen :=
  o991Gen_of_inputs
    (nineSevenTwoInputGen_of_kFacts Section15.kFactThreeFiveInner_holds
      CFSG.LocalAnalysis.RankThreeUC.S15.K37.kFactThreeSevenTwoThree_holds)
    (nineSixInputGen_of_nineSixMoreoverGen
      (nineSixMoreoverGen_of_kFactThreeFiveCentral K35Central.kFactThreeFiveCentral_holds))
    threeFiveA11InputGen_holds zkFacts_holds

section


theorem nineNineOneInput_holds : NineNineOneInput :=
  nineNineOneInput_of_o991Gen o991Gen_holds nineSevenOneGen_holds

end

end

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
