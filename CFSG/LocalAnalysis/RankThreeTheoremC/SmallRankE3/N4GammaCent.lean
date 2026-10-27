module

public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def GammaCentP : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (P : Sylow p X) (x : X),
    CFSG.AGLEmbedding.CatalogSimpleSections X → x ∈ (P : Subgroup X) → x ≠ 1 → x ^ p = 1 →
    Open.pRank p (P : Subgroup X) = 3 → Open.pRank p (centralizer ({x} : Set X)) = 2 →
    (∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤) →
    (∀ Q : Subgroup X, Q ≠ ⊥ → IsPGroup 2 Q → Open.pRank 3 (normalizer (Q : Set X)) ≤ 3) →
    (∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) →
    CFSG.HallHigman.IsPSolvable p (centralizer ({x} : Set X))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
