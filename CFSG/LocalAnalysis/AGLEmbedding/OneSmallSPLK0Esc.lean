module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.card_sylow_eq_card_liftX (hd : D1OneSmallData p P M H R Rbar K)
    {T : Sylow p K} (hT : (T : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :
    Nat.card (T : Subgroup K) = Nat.card (d1LiftX p H R K) := by
  have hp := hd.cfg.red.prime
  have hXp : IsPGroup p ((d1LiftX p H R K).subgroupOf H) :=
    (hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)).comap_subtype
  rw [← Subgroup.card_map_of_injective K.subtype_injective, hT, ← hd.cfg.map_d1LiftX_eq_inf,
    card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hXp,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (d1LiftX_le_H p H R K)).toEquiv]

end CFSG.AGLEmbedding
