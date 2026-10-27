module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KappaTop

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoCentral3InnerK (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    D1KappaIH p M H →
    ∀ z : H, D1CaseTwoCand p M H R z →
      (∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)) →
      ¬ D1CaseTwoAlphaR p M H R → False

@[expose] def D1CaseTwoCentral3InnerNotQK (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    D1KappaIH p M H →
    ∀ z : H, D1CaseTwoCand p M H R z →
      (∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)) →
      ¬ D1CaseTwoAlphaR p M H R →
      ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
        ¬ L ≤ d1X0 p M H → ∀ E : Subgroup G, IsFieldOmegaA p M H R L E →
          ¬ rankThreeGamma 1 p E ≤ M

end CFSG.LocalAnalysis.RankThreeTheoremC
