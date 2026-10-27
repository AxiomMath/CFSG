module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData.toPhaseThree (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoData p P M H R Rbar) : D1PhaseThree p P M H R :=
  hd.toAt.toPhaseThree (kFactCycAut_of_kFactBeta hβ) hS hKL

theorem D1CaseTwoData.d1LayerX_ne_bot (hd : D1CaseTwoData p P M H R Rbar) :
    d1LayerX p H R ≠ ⊥ :=
  hd.toAt.d1LayerX_ne_bot

theorem D1CaseTwoData.isSimpleGroup (hd : D1CaseTwoData p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤) :
    IsSimpleGroup L :=
  hd.toAt.isSimpleGroup hL

theorem D1CaseTwoData.map_d1LayerX_inf_ne_bot (hd : D1CaseTwoData p P M H R Rbar)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (hL : IsComponentOf L ⊤) :
    ((d1LayerX p H R).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
      L ≠ ⊥ :=
  hd.toAt.map_d1LayerX_inf_ne_bot L hL

theorem D1CaseTwoData.map_nclIn_eq (hd : D1CaseTwoData p P M H R Rbar) {Y : Subgroup G}
    (hYX : Y ≤ d1LayerX p H R)
    (hY : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥) :
    ((nclIn H Y).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      CFSG.layer (H ⧸ primeComplementCore (G := H) p) :=
  hd.toAt.map_nclIn_eq hYX hY

theorem D1CaseTwoData.not_le_of_nclIn_le (hβ : KFactBeta) (hd : D1CaseTwoData p P M H R Rbar)
    {H' : Subgroup G} (hJH' : nclIn H (d1LayerX p H R) ≤ H') : ¬ H' ≤ M :=
  hd.toAt.not_le_of_nclIn_le (kFactCycAut_of_kFactBeta hβ) hJH'

theorem D1CaseTwoData.nclIn_nclIn (hd : D1CaseTwoData p P M H R Rbar) :
    nclIn (nclIn H (d1LayerX p H R)) (d1LayerX p H R) = nclIn H (d1LayerX p H R) :=
  hd.toAt.nclIn_nclIn

theorem D1CaseTwoData.d1LayerX_le_nclIn (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoData p P M H R Rbar)
    (hmeet : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥) :
    d1LayerX p H R ≤ nclIn H (pCorePreimage p M ⊓ d1LayerX p H R) :=
  hd.toAt.d1LayerX_le_nclIn (kFactCycAut_of_kFactBeta hβ) hS hKL h84 hD2 hmeet

end Data

end CFSG.AGLEmbedding
