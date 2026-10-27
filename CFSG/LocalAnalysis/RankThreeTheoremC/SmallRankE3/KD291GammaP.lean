module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def GammaConclusionP (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x : X) :
    Prop :=
  ∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), L.Normal ∧ IsSimpleGroup L ∧
    (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup L ∧ ¬ IsLinearOrUnitaryAt p L ∧
    centralizer (L : Set (X ⧸ primeComplementCore (G := X) p)) = ⊥ ∧
    (QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p) ∈ L ∧
    ∀ z : X, z ∈ centralizer ((P : Subgroup X) : Set X) → z ∈ (P : Subgroup X) → z ^ p = 1 →
      (QuotientGroup.mk z : X ⧸ primeComplementCore (G := X) p) ∈ L

@[expose] def GammaStructureP : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (P : Sylow p X) (x : X),
    CFSG.AGLEmbedding.CatalogSimpleSections X → x ∈ (P : Subgroup X) → x ≠ 1 → x ^ p = 1 →
    Open.pRank p (P : Subgroup X) = 3 → Open.pRank p (centralizer ({x} : Set X)) = 2 →
    (∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤) →
    (∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) →
    GammaConclusionP p X P x

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
