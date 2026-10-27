module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoNoSP {G : Type} [Group G] [Finite G] (p : ℕ) (M H R : Subgroup G) :
    Prop :=
  ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
    ¬ L ≤ d1X0 p M H → ∀ z : H, (z : G) ∈ R → orderOf (z : G) = p →
      R ≤ Subgroup.centralizer ({(z : G)} : Set G) →
      QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
        Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)) →
      ¬ D1CzSP p (z : G)

@[expose] def D1CaseTwoSP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1CaseTwoNoSP p M H R

end CFSG.AGLEmbedding
