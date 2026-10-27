module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeDataBranchA
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeCorrectedThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineSocleHolds
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeOrders
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeBranchNotLe
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenInputsHolds
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineNineOneHolds
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.HardMathSupport.Foote.Coordinator.Downstream
public import CFSG.CGT.PushingUpLit.TwoKHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeBranchB
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeBranchC
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenTorusExclusionProof
public import CFSG.CGT.PushingUpLit.BHS6.NestedBasic
public import CFSG.CGT.T75P.Ctx
public import CFSG.CGT.T75P.DecA
public import CFSG.CGT.Timmesfeld75.SimpleAssembly
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J3
public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c
public import CFSG.GH74.Generic.S45.LEvSporFacts
public import CFSG.GroupTheory.CoprimeLiftElementaryAbelian
public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Rest
public import CFSG.LieType.OutStructureLinearDiagonal
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHS
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssembly
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGTools
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporHe
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6Graph
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch12Sec6KGComp
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSL3B
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate12632
public import Certificates.Certificate12680
public import Certificates.Certificate17633
public import Certificates.Certificate19764
public import Certificates.Certificate19766
public import Certificates.Certificate34002
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteRankThree
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.Notation
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


theorem twelveThreeData_of_twelveCtx (h39 : ThreeNine) (h : TwelveCtx G M p Q H) :
    ∀ d ∈ sigmaSet G M, d ∣ Nat.card (H ⊓ M : Subgroup G) → TwelveThreeData M p H d := by
  intro d hd hdH
  have h1 := CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
  have h2 := CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
  have h25 := CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
  have h84 := CFSG.AGLEmbedding.asc81bEightFour_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h10 := nineTenGen_holds
  have h310 := CFSG.LocalAnalysis.AGL81I.Section3.threeTen_holds
  have hI := CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nineNineOneInput_holds
  have hns := not_isSolvable_of_twelveCtx h1 h2 h25 h84 h
  by_cases hA : pLayerIn p H ≤ M
  · by_cases hbot : pLayerIn p H = ⊥
    · by_cases hp3 : p = 3
      · exact (false_of_branchC_three h10 h310 hI twelveThreeCorrectedThreeFacts_holds h hns hd
          hdH hbot hp3).elim
      · exact twelveThreeData_of_branchC h10 h310 hI h hns hd hdH hbot hp3
    · exact (false_of_nineTen_branchB h10 h310 hI h hns hd hdH hbot hA).elim
  · exact twelveThreeData_of_branchA h10 h39 hI CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge
      kFactThreeNineSocle_holds twelveThreeOrderFacts_holds kFactFi22SectionThreeRank_holds h hns hd
      (not_dvd_card_xSub_inf_of_twelveCtx h1 h2 h25 h84 h hI hd) hdH hA

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
