module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def KFactStrongThreeAutomizer : Prop :=
  ∀ (N : Type) [Group N] [Finite N], Open.IsKGroup N → ∀ N₀ : Subgroup N,
    GLBStronglyEmbedded 3 N₀ → Open.pRank 3 N₀ = 2 →
    ∀ R : Subgroup N, R ≤ N₀ → IsPGroup 3 R → ¬ 3 ∣ R.relIndex N₀ →
      ((∀ a ∈ R, ∀ b ∈ R, a * b = b * a) →
          IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
            IrreducibleOn (N₀ ⊓ Subgroup.normalizer (R : Set N)) R) ∧
      (¬ 2 ∣ N₀.index →
          IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
            TransitiveOnNonidentity (N₀ ⊓ Subgroup.normalizer (R : Set N)) R)

end CFSG.AGLEmbeddingD2.McLaughlin
