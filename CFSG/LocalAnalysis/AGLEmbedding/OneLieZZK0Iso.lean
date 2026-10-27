module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBPhase
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Sylow

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem toEsc (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) :
    D1OneLieEscData p P M H R Rbar K P' H₁ S :=
  ⟨hc.data, hc.escape, hc.nclIn_le⟩

theorem exists_sylow_of_mulEquiv (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩) :
    ∃ T₁ : Sylow p L, (T₁ : Subgroup L).map L.subtype =
      ((d1LiftX p H R K).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
  hc.toEsc.exists_sylow_of_mulEquiv hJL ψ hψ

theorem oneLieFacts_of_mulEquiv (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hK : KFactOneLie) {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hLs : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) (hLcat : IsCatalogGroup L)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩)
    (T₁ : Sylow p L) (hT₁ : (T₁ : Subgroup L).map L.subtype =
      ((d1LiftX p H R K).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) :
    OneLieFacts p L T₁ ∧ (GLBCore p 1 (T₁ : Subgroup L)).map L.subtype ≤
      ((H₁ ⊓ M).subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
  hc.toEsc.oneLieFacts_of_mulEquiv hK hLs hLnab hLcat hJL ψ hψ T₁ hT₁

end D1OneLieKZeroData

end CFSG.AGLEmbedding
