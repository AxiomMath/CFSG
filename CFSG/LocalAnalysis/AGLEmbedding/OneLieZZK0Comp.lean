module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBComponent

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1KZeroCore

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem exists_component_le (hc : D1KZeroCore p P M H R Rbar K P' H₁ S)
    (hSch : KFactCatalogSchreier) (hcon : ¬ HasPrimeConstraint (G := H₁) p) :
    ∃ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ ∧ L.Normal ∧
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L :=
  hc.data.exists_component_le_of_escape hc.kProper hc.escape hc.nclIn_le hc.liftX_le hSch hcon

end D1KZeroCore

namespace D1OneLieKZeroData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem exists_component_le (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hSch : KFactCatalogSchreier) (hcon : ¬ HasPrimeConstraint (G := H₁) p) :
    ∃ L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p), IsComponentOf L ⊤ ∧ L.Normal ∧
      ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) ≤ L :=
  hc.toCore.exists_component_le hSch hcon

end D1OneLieKZeroData

end CFSG.AGLEmbedding
