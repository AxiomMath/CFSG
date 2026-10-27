module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterNode
import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.HardMathSupport.Curtis.Coordinator Subgroup
open scoped commutatorElement

namespace InnerQ

section Generic

variable {X : Type*} [Group X]

instance pCoreOf_two_normal (V : Subgroup X) : ((pCoreOf 2 V).subgroupOf V).Normal := by
  rw [CFSG.openPCoreOf_subgroupOf]
  exact CFSG.pCore_normal

end Generic

end InnerQ

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC
