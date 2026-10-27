module

import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem coprime_of_mk_inclusion_eq_one3 {H' W : Subgroup G} (hWH : W ≤ H') (w : W)
    (hw : QuotientGroup.mk' (primeComplementCore (G := H') p) (Subgroup.inclusion hWH w) = 1) :
    p.Coprime (orderOf w) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw
  have h2 := Subgroup.orderOf_dvd_natCard _ hw
  rw [orderOf_injective _ (Subgroup.inclusion_injective hWH)] at h2
  exact (primeComplementCore_coprime (G := H') p).coprime_dvd_right h2

end CFSG.LocalAnalysis.RankThreeTheoremC
