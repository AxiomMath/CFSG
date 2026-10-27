module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def NormalizerMovesLines (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ t ∈ (S : Subgroup K), t ≠ 1 →
    ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * t * n⁻¹ ∉ Subgroup.zpowers t

structure SecondPointFacts (p : ℕ) (Q : Type) [Group Q] [Finite Q] : Prop where
  autBound : ∀ (S : Sylow p Q) (A : Subgroup (MulAut Q)), IsPGroup p A →
    Nat.card A ∣ Nat.card (S : Subgroup Q)
  shape : (SylowIsPlane p Q ∧ NormalizerMovesLines p Q) ∨
    (SylowIsHeisenberg p Q ∧ NormalizerTransitiveCenter p Q)


end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
