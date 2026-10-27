module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure L62Data (X : Type) [Group X] [Finite X] (S : Sylow 3 X) (x z : X) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  rank : CFSG.Open.pRank 3 (S : Subgroup X) = 3
  x_mem : x ∈ (S : Subgroup X)
  x_ne : x ≠ 1
  x_pow : x ^ 3 = 1
  cent : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) ≤ 2
  z_mem : z ∈ (S : Subgroup X)
  z_central : ∀ g ∈ (S : Subgroup X), g * z = z * g
  z_ne : z ≠ 1
  z_pow : z ^ 3 = 1
  z_gen : ∀ w ∈ (S : Subgroup X), (∀ g ∈ (S : Subgroup X), g * w = w * g) → w ^ 3 = 1 →
    w ∈ zpowers z
  no_normal_three : ∀ N : Subgroup X, N.Normal → N.index ≠ 3
  qrank : ∀ q : ℕ, q.Prime → 5 ≤ q → CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2

structure L62Bar (H : Type) [Group H] [Finite H] (S : Sylow 3 H) (x z : H) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections H
  core : primeComplementCore (G := H) 3 = ⊥
  rank : CFSG.Open.pRank 3 (S : Subgroup H) = 3
  rank_top : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3
  x_mem : x ∈ (S : Subgroup H)
  x_ne : x ≠ 1
  x_pow : x ^ 3 = 1
  cent : CFSG.Open.pRank 3 (centralizer ({x} : Set H)) ≤ 2
  z_mem : z ∈ (S : Subgroup H)
  z_central : ∀ g ∈ (S : Subgroup H), g * z = z * g
  z_ne : z ≠ 1
  z_pow : z ^ 3 = 1
  z_gen : ∀ w ∈ (S : Subgroup H), (∀ g ∈ (S : Subgroup H), g * w = w * g) → w ^ 3 = 1 →
    w ∈ zpowers z
  no_normal_three : ∀ N : Subgroup H, N.Normal → N.index ≠ 3

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
