module

public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeK
public import CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem noXBlock_of_standingGen
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (hS : StandingGen G) :
    ∀ M Y : Subgroup G, GLBIsMaxTwoLocal M → Y ≤ M → IsSubnormal Y M →
      InClassXBlock Y → False := by
  intro M Y hM hYM hsub hY
  have hrank : 3 ≤ CFSG.Assembly.evenRank G :=
    (CFSG.AGLEmbedding.NoXBlock.open_evenRank_eq (G := G)) ▸ hS.rank
  have hle := CFSG.AGLEmbedding.NoXBlock.evenRank_le_two_of_inOmegaK h1 h2 h25
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp hS.kProper)
    hS.simple (CFSG.AGLEmbedding.NoXBlock.assembly_isCharTwoType_of_open hS.charTwo)
    ⟨CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hY, M,
      CFSG.AGLEmbedding.NoXBlock.isMaximalTwoLocal_of_glb hM, hYM,
      CFSG.AGLEmbedding.NoXBlock.isSubnormal_subgroupOf_of_open hsub⟩
  omega

theorem noXBlockFor_of_standingGen
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (hS : StandingGen G) :
    CFSG.AGLEmbeddingD2.NoXBlockFor G :=
  noXBlock_of_standingGen h1 h2 h25 hS

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
