module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData3.toPhaseThree (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoData3 p P M H R Rbar) : D1PhaseThree p P M H R :=
  hd.toAt.toPhaseThree (kFactCycAut_of_kFactOutCyclic hOut) hS hKL

theorem D1CaseTwoData3.map_d1LayerX_inf_ne_bot (hd : D1CaseTwoData3 p P M H R Rbar)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (hL : IsComponentOf L ⊤) :
    ((d1LayerX p H R).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
      L ≠ ⊥ :=
  hd.toAt.map_d1LayerX_inf_ne_bot L hL

theorem D1CaseTwoData3.map_nclIn_eq (hd : D1CaseTwoData3 p P M H R Rbar) {Y : Subgroup G}
    (hYX : Y ≤ d1LayerX p H R)
    (hY : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥) :
    ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      CFSG.layer (H ⧸ primeComplementCore (G := H) p) :=
  hd.toAt.map_nclIn_eq hYX hY

theorem D1CaseTwoData3.not_le_of_nclIn_le (hOut : KFactOutCyclic)
    (hd : D1CaseTwoData3 p P M H R Rbar)
    {H' : Subgroup G} (hJH' : nclIn H (d1LayerX p H R) ≤ H') : ¬ H' ≤ M :=
  hd.toAt.not_le_of_nclIn_le (kFactCycAut_of_kFactOutCyclic hOut) hJH'

end Data

end CFSG.LocalAnalysis.RankThreeTheoremC
