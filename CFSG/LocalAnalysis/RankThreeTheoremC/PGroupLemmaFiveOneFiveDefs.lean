module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

@[expose] def IsExtraspecialExpP (p : ℕ) {G : Type} [Group G] (Y : Subgroup G) : Prop :=
  ¬ IsMulCommutative Y ∧ Nat.card Y = p ^ 3 ∧ ∀ y ∈ Y, y ^ p = 1

@[expose] def PGroupRankTwoCharSubgroup (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ Q : Subgroup G, IsPGroup p Q → pRank p Q = 2 →
    ∃ Y : Subgroup G, Y ≤ Q ∧
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
      2 ≤ pRank p Y ∧ ((IsElemAbelian p Y ∧ Nat.card Y = p ^ 2) ∨ IsExtraspecialExpP p Y)

end CFSG.LocalAnalysis.RankThreeTheoremC
