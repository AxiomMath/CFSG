module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic
import CFSG.CGT.PushingUpLit.Transport
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81EightThirteen (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → 3 ∈ rankThreeSigmaA G →
  ∀ (P : Sylow 3 G) (M H : Subgroup G), GLBIsMaxTwoLocal M →
    GLBWeakCore 3 (P : Subgroup G) ≤ M → GLBIsMaxTwoLocal H → H ≠ M →
    Open.pRank 3 (H ⊓ M) = 3 →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ → ¬ IsLinThreeFour K

variable {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

end CFSG.LocalAnalysis.RankThreeTheoremC
