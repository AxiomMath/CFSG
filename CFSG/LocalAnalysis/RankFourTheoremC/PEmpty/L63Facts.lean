module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane IsMaxTwoInvariantIn)
open CFSG.AGLEmbedding (CatalogSimpleSections)

structure Plane63 (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  catalog : CatalogSimpleSections X
  plane : SmallRankPlane p (P : Subgroup X) x z
  z_central : z ∈ centralizer ((P : Subgroup X) : Set X)
  four_le : 4 ≤ Open.pRank p (P : Subgroup X)
  rank_centralizer : Open.pRank p (centralizer ({x} : Set X)) ≤ 2
  sylow_centralizer : CFSG.ABGLocalTools.IsSylowOf p
    ((P : Subgroup X) ⊓ centralizer ({x} : Set X)) (centralizer ({x} : Set X))
  perfect : ∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤

@[expose] def KFactSingleComponent : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X), Plane63 p X P x z →
    (∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) →
    (∀ T : Subgroup X, IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) ⊤ T →
        Open.pRank p (P : Subgroup X) ≤ Open.pRank p (normalizer (T : Set X))) ∨
      (∀ W : Subgroup X, Nat.Coprime p (Nat.card W) →
        zpowers x ⊔ zpowers z ≤ normalizer (W : Set X) → W ≤ primeComplementCore (G := X) p)

@[expose] def KFactMultiComponent : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X), Plane63 p X P x z →
    (∃ L K : Subgroup (X ⧸ primeComplementCore (G := X) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K ⊤ ∧ L ≠ K) →
    ∀ T : Subgroup X, IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) ⊤ T →
      Open.pRank p (P : Subgroup X) ≤ Open.pRank p (normalizer (T : Set X))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
