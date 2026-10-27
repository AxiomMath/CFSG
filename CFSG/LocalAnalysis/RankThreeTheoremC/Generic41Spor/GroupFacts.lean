module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcL
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcLTrans
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcLLem45Sound
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcLLemma45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupJ4
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupJ4Trans
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupJ4Lemma45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32Loc
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32Lemma45
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4RRepBase
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Sporadic.J4.QT2LocCntMainBase
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2269
public import Certificates.Data.HSFiveCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

section Tits


theorem tits_gfree : TitsFacts := titsFacts_holds

end Tits

theorem a10_gfree : A10Facts := a10Facts_holds

section McL


theorem mcl_lemma45_of_check
    (hchk : McLLem45.check Certificates.MaxD2Heis.mclFiveDataP McLLem45.wordW McLLem45.tree = true) :
    Lemma45Facts IsMcLType 5 McLShape :=
  mcl_lemma45_of_model (mclLem45Model_of_check hchk)

theorem mcl_gfree
    (hchk : McLLem45.check Certificates.MaxD2Heis.mclFiveDataP McLLem45.wordW McLLem45.tree = true) :
    ExtraFacts IsMcLType 5 McLShape :=
  extraFacts_mcl mclFacts_holds ⟨mcl_transCenter, mcl_lemma45_of_check hchk⟩

end McL

section J4


theorem j4_gfree : ExtraFacts IsJ4Type 11 J4Shape :=
  extraFacts_j4 j4Facts_holds ⟨j4_transCenter, j4_lemma45⟩

end J4

section Sz32


theorem sz32_gfree : Sz32Facts ∧ Sz32OpenFacts :=
  ⟨sz32Facts_holds, ⟨sz32_transOmega, sz32_maximal, sz32_lemma45⟩⟩

end Sz32

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
