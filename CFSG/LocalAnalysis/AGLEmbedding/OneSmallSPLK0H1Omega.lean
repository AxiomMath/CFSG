module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0SmallKFact

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.card_map_liftX (hd : D1OneSmallData p P M H R Rbar K)
    (hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)) {H₁ : Subgroup G}
    (hXH₁ : d1LiftX p H R K ≤ H₁) :
    Nat.card (((d1LiftX p H R K).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p))) = p ^ 2 := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p (d1LiftX p H R K) := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hXcard : Nat.card (d1LiftX p H R K) = p ^ 2 := by
    obtain ⟨T, hT, -⟩ := hd.exists_sylow
    rw [← hd.card_sylow_eq_card_liftX hT, (sylow_facts_of_pair hLA T).1]
  have h1 := card_map_mk_of_isPGroup hp (primeComplementCore (G := H₁) p)
    (primeComplementCore_coprime p)
    (show IsPGroup p ((d1LiftX p H R K).subgroupOf H₁) from hXp.comap_subtype)
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH₁).toEquiv, hXcard]

end CFSG.AGLEmbedding
