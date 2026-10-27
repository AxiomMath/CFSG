module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenThreeThreeTwelveCtx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTwelveKerHolds
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.O812sixFi22
public import Certificates.Certificate2124
public import Certificates.Certificate2126
public import Certificates.Certificate8126
public import Certificates.Certificate17633
public import Certificates.Certificate19830
public import Certificates.Certificate19831
public import Certificates.Certificate19840
public import Certificates.Certificate19842
public import Certificates.Certificate19843
public import Certificates.Certificate19850
public import Certificates.Certificate19851
public import Certificates.Certificate19852
public import Certificates.Certificate31072
public import Certificates.Certificate465005
public import Certificates.Certificate753501
public import Certificates.Certificate753502
public import Certificates.Certificate753503
public import Certificates.Certificate753504
public import Certificates.Certificate753505
public import Certificates.Certificate753506
public import Certificates.Certificate753521
public import Certificates.Certificate753522
public import Certificates.Certificate1322001
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneAssembly
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourBlockFactsOf
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourJLeXSpor
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeDataOf
import CFSG.HardMathSupport.Foote.Coordinator.Downstream
import CFSG.CGT.PushingUpLit.TwoKHolds
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.NineThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineNineOneHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveThirteenKerHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.KFactFi22SPEHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactParabolicWCentHolds
import CFSG.RankThree.PartOne.TCB.SchreierFinal
import CFSG.LocalAnalysis.AGL81I.Section4.FourNineteenHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitLines
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutFix
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0ShapeFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.MonsterRows
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf
import CFSG.CGT.PushingUpLit.BHS.ThreeEight
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightBT
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightGaps
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4U3Out
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGU
import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGU
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldG2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutModels
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrime
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenGlue
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenType
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BaumComponent
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymDefs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubReduce
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubSympBlocks
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Assembly
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.Quasithin.Background.C126Split2
import CFSG.RankThree.PartOne.S11c.Sec66E6
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}


theorem twelveFourOne_of_twelveCtx_of_threeNine (h39 : ThreeNine) (h : TwelveCtx G M p Q H)
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G) := by
  have h1 := CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
  have h2 := CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
  have h25 := CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
  have h93 := CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.asc81bNineThree_holds
  have hN1 := CFSG.LocalAnalysis.AGL81I.Section4.agl81FourNineteen_holds
  exact twelveFourOne_of_twelveThreeData h1 h2 h25
    (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
        CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
    (CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs
        CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved))
    h93 Section14.nineNineOneInput_holds
    (nineTwelveKerGen_holds Section14.nineTwelveThirteenRankThree_holds)
    (Section8.o812sixGen_of_fi22 Section8.kFactFi22SPEThreeRank)
    kFactParabolicWCentSolvable_holds CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds hN1
    (kFactOddAutParabolicFixPrime_of_general kFactOddAutParabolicFix_holds)
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement)
    h hsyl (fun L hL => twelveFourBlockFacts_of_twelveCtx h1 h2 h25 h93 hN1 h hL)
    (fun L hL hM3 b hb hbL hbo hbJ => tenThreeThree_of_twelveCtx h hM3 hL hb hbL hbo hbJ)
    (fun d hdat hs L hL => jOne_le_xSub_of_caseSpor h hdat hs hL)
    (twelveThreeData_of_twelveCtx h39 h)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
