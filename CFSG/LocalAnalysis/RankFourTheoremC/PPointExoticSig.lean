module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSz
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigTits
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigMcL
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigJ4
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Foundations
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4.QT2LocCntProof
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2269
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Data.HSFiveCheck

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem signalizerAutAt_of_exoticFive
    {p : ℕ} {i : TauCeti.CFSGIndex} (h : ExoticFive p i) : SignalizerAutAt p i := by
  cases h with
  | alt h hp => exact signalizerAutAt_alt h hp
  | suzuki hp hd => exact signalizerAutAt_suzuki hp hd
  | tits hp hd => exact signalizerAutAt_tits hp hd
  | mcl hp => exact signalizerAutAt_mcl hp
  | jFour hp => exact signalizerAutAt_jFour hp

end CFSG.LocalAnalysis.RankFourTheoremC
