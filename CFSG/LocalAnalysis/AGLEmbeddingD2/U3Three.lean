module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def D2U3ThreeStrong : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (p : ℕ), (p = d.1.characteristic ∧ p = 3) →
    ∀ (P : Sylow p G) (M A H R : Subgroup G), D2Escape p P M A H R →
    D2EscapeMax p P M R → p ∈ GLBBetaFour G →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → GLBStronglyEmbedded 3 M → False

end CFSG.AGLEmbeddingD2
