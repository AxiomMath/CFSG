module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank

theorem D1Escape.false_of_klingen (hβ : KFactBeta) (hα : KFactAlphaW) {G : Type} [Group G]
    [Finite G] (hglob : D1Global G) {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G}
    (hloc : D1Local p P M) (h : D1Escape p P M H R)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (hRbar : (Rbar : Subgroup _) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))) : False := by
  obtain ⟨z, hz⟩ := h.centralizerInput_of_klingen hloc Rbar hRbar hK
  exact false_of_centralizerInput_of_kFactsW hβ hα hglob.simple hglob.nonab hglob.kProper hz

end CFSG.AGLEmbedding
