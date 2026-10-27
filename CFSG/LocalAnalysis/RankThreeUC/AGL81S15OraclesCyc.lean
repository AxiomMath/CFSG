module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def cHatImage (G : Type) [Group G] [Finite G] (M T : Subgroup G) :
    Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
  (gnC (T.subgroupOf M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

@[expose] def CycHat (G : Type) [Group G] [Finite G] (M T : Subgroup G) : Prop :=
  ∀ r : ℕ, r.Prime → 3 < r → IsCyclic ↥(pCoreOf r (cHatImage G M T))

end CFSG.LocalAnalysis.RankThreeUC.S15
