module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZData

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Transport

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.unitary_sylow (hd : D1OneSmallData p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) {n : ℕ}
    (hTcard : Nat.card (T₁ : Subgroup K) = p ^ (3 * n))
    (hTcomm : ⁅(T₁ : Subgroup K), (T₁ : Subgroup K)⁆ =
      (T₁ : Subgroup K) ⊓ Subgroup.centralizer ((T₁ : Subgroup K) : Set K))
    (hTpow : ∀ u ∈ (T₁ : Subgroup K), u ^ p = 1) :
    d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) =
        d1LiftX p H R K ⊓ Subgroup.centralizer (d1LiftX p H R K : Set G) ∧
      ⁅d1LiftX p H R K, d1LiftX p H R K⁆ =
        d1LiftX p H R (centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) ∧
      Nat.card (d1LiftX p H R K) = p ^ (3 * n) ∧ ∀ u ∈ d1LiftX p H R K, u ^ p = 1 :=
  hd.toCore.unitary_sylow hT₁ hTcard hTcomm hTpow

end Transport

end CFSG.AGLEmbedding
