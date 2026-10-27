module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescPlan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HTD42Outer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264tTD42Three
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieHolds
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveHN
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveShape
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2ModelDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycFive
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycUnique
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFRest
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZ
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescCTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1113
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQResidueLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3NFAxis
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Close
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38K0
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA

structure I264bResidual3 : Prop where
  td42_7 : TD42SevenRank
  u38_3 : KDescFam 3 fU38
  linear : ∀ p, HDesc.KDescFamRes p fLinear
  unitary : ∀ p, HDesc.KDescFamRes p fUnitary
  symplectic : ∀ p, HDesc.KDescFamRes p fSymplectic
  omegaPlus : ∀ p, HDesc.KDescFamRes p fOmegaPlus
  omegaMinus : ∀ p, HDesc.KDescFamRes p fOmegaMinus
  e6 : ∀ p, HDesc.KDescFamRes p fE6
  e7 : ∀ p, HDesc.KDescFamRes p fE7
  e8 : ∀ p, HDesc.KDescFamRes p fE8
  f4 : ∀ p, HDesc.KDescFamRes p fF4
  g2 : ∀ p, HDesc.KDescFamRes p fG2
  twE6 : ∀ p, HDesc.KDescFamRes p fTwE6
  triD4 : ∀ p, HDesc.KDescFamRes p fTriD4
  reeTits : ∀ p, HDesc.KDescFamRes p fReeTits

section I264bRes3


theorem i264bResidual2_of_3 (hR : KD264Lie.KD264LieRest7) (h : I264bResidual3) : I264bResidual2 :=
  HDesc.i264bResidual2_of_klie (KD264Lie.kd264KLie_holds (KD264Lie.kd264LieInputs_of_rest7 hR))
    (kDescFam_td42_three_of_residual TD42OuterFix_holds) h.td42_7 h.u38_3 h.linear h.unitary h.symplectic
    h.omegaPlus h.omegaMinus h.e6 h.e7 h.e8 h.f4 h.g2 h.twE6 h.triD4 h.reeTits

end I264bRes3

end CFSG.LocalAnalysis.GLTheoremA

end
