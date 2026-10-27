module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ADefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Cz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.map_d1LiftX_eq_inf (hd : D1OneSmall3Data p P M H R Rbar K) :
    ((d1LiftX p H R K).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
  rw [map_d1LiftX, hd.cfg.rbar]

end Cz

end CFSG.LocalAnalysis.RankThreeTheoremC
