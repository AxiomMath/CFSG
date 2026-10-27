module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def SporGammaOneAt (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) = ⊤

end CFSG.AGLEmbedding
