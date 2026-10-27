module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def TwelveFour (M H : Subgroup G) : Prop :=
  ∀ d : ℕ, d ∈ sigmaSet G M →
    (¬ d ∣ Nat.card (H ⊓ M : Subgroup G)) ∧ 3 < d ∧ ¬ (3 ∈ sigmaSet G M)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
