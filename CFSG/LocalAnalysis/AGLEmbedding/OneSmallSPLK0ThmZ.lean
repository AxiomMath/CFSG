module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.d1PlusCore_facts (hd : D1OneSmallData p P M H R Rbar K) :
    d1PlusCore p H K ≤ H ⊓ M ∧ H ≤ Subgroup.normalizer (d1PlusCore p H K : Set G) ∧
      GLBPrimeCore p H ≤ d1PlusCore p H K :=
  hd.toCore.d1PlusCore_facts

end CFSG.AGLEmbedding
