module

public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem R_le_inf (h : AGLPair p M H R) : R ≤ H ⊓ M :=
  le_inf h.le_H h.le_M

theorem twoCore_M_le_glbPrimeCore (h : AGLPair p M H R) : pCoreOf 2 M ≤ GLBPrimeCore p H :=
  h.twoCore_M_le.trans h.twoCore_le_primeCore

theorem normalizer_thompsonJ_eq (h : AGLPair p M H R) :
    M ⊓ Subgroup.normalizer (thompsonJ (pCoreOf 2 H) : Set G) = H ⊓ M ∧
      Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) = H :=
  h.toTwoLocalPair.normalizer_thompsonJ_eq

theorem omegaOneCenter_le (h : AGLPair p M H R) :
    omegaOneCenterOf (pCoreOf 2 H) ≤ omegaOneCenterOf (pCoreOf 2 M) ∧
      M ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) ≤ H ⊓ M :=
  h.toTwoLocalPhaseThree.omegaOneCenter_le

end AGLPair

end CFSG.AGLEmbeddingD2
