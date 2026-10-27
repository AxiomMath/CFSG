module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

@[expose] def KFactM11SylowTransitive : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) →
    ∀ (S : Sylow 3 K) (a b : K), a ∈ (S : Subgroup K) → b ∈ (S : Subgroup K) → a ≠ 1 → b ≠ 1 →
      ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * a * n⁻¹ = b

end CFSG.LocalAnalysis.RankThreeTheoremC
