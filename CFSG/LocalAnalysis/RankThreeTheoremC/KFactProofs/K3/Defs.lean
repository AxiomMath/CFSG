module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

abbrev W3 : Type := Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

@[expose] def KFactConstraintCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    primeComplementCore (G := X) 3 = ⊥ →
    ∀ L : Subgroup X, IsComponentOf L ⊤ → (∀ K : Subgroup X, IsComponentOf K ⊤ → K = L) →
    ∀ S : Sylow 3 X, Nonempty ((S : Subgroup X) ≃* W3) →
    (∃ x ∈ (S : Subgroup X), x ≠ 1 ∧ x ^ 3 = 1 ∧
      CFSG.Open.pRank 3 (centralizer ({x} : Set X)) ≤ 2) →
    ∃ N : Subgroup X, N.Normal ∧ N.index = 3

@[expose] def K3LiftThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ S : Sylow 3 (Bar X), Nonempty ((S : Subgroup (Bar X)) ≃* W3) →
    ∀ L : Subgroup (Bar X), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Bar X), IsComponentOf K ⊤ →
        ∃ g ∈ (S : Subgroup (Bar X)), K = L.map (MulAut.conj g).toMonoidHom) →
      ¬ (S : Subgroup (Bar X)) ≤ normalizer (L : Set (Bar X)) →
      ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ 3 ≤ CFSG.Open.pRank q (⊤ : Subgroup X)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
