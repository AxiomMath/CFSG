module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Star

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_normalizer_vz_le {p : ℕ} {z : G} {Hs : Subgroup G}
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs) :
    Subgroup.centralizer ({z} : Set G) ≤ Hs :=
  (Subgroup.le_normalizer.trans
    (normalizer_le_normalizer_pCoreOf_glbPrimeCore p (Subgroup.centralizer ({z} : Set G)))).trans
      hLHs

end Star

end CFSG.AGLEmbedding
