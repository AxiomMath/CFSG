module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

structure D1CaseTwoDataU (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfig3 p P M H R Rbar
  cyclic : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
    IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
      Subgroup (H ⧸ primeComplementCore (G := H) p))

theorem D1CaseTwoData3.toU {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoData3 p P M H R Rbar) :
    D1CaseTwoDataU p P M H R Rbar :=
  ⟨hd.cfg, hd.cyclic⟩

theorem D1CaseTwoDataU.rank {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoDataU p P M H R Rbar) :
    Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 :=
  hd.cfg.pRank_rbar_eq_three

end CFSG.LocalAnalysis.RankThreeTheoremC
