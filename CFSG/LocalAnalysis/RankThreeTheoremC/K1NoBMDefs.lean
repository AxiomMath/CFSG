module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

@[expose] def NotBM (K : Type) [Group K] : Prop :=
  ¬ Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.B).Group) ∧
    ¬ Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M).Group)

@[expose] def StronglyEmbeddedRankTwoKFactNoBM : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → NotBM K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      CFSG.Open.pRank p (T : Subgroup K) = 2 → rankThreeGamma 1 p (T : Subgroup K) ≠ ⊤ →
      IsRankTwoSEGroup p K

end CFSG.LocalAnalysis.RankThreeTheoremC
