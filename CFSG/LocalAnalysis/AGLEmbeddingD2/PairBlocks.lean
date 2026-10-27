module

import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding
open scoped commutatorElement

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R L : Subgroup G}

theorem exists_weakSBlock (h : AGLPair p M H R) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L :=
  h.toTwoLocalPhaseThree.exists_weakSBlock h.isKGroup.1 h84 hD2

theorem not_isSylowTwoOf_inf (h : AGLPair p M H R) (h85 : Asc81bEightFive) (hD2 : NoXBlockFor G)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : ¬ IsSylowTwoOf (pCoreOf 2 H ⊓ L) L :=
  h.toTwoLocalPhaseThree.not_isSylowTwoOf_inf h.isKGroup.1 h85 hD2 hL

theorem weakSBlock_asc81bHyp (h : AGLPair p M H R) (h86 : Asc81bEightSix)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) ∧
      Asc81bHyp (L ⊔ pCoreOf 2 H) (pCoreOf 2 H) :=
  h.toTwoLocalPhaseThree.weakSBlock_asc81bHyp h.isKGroup.1 h86 hL

theorem blockV_facts (h : AGLPair p M H R) (h86 : Asc81bEightSix)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    pCoreOf 2 M ≤ pCoreOf 2 (L ⊔ pCoreOf 2 H) ∧ pCoreOf 2 (L ⊔ pCoreOf 2 H) ≤ pCoreOf 2 H ∧
      omegaOneCenterOf (pCoreOf 2 H) =
        blockV (pCoreOf 2 H) L ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      (L ⊔ pCoreOf 2 H) ⊓ Subgroup.centralizer (blockV (pCoreOf 2 H) L : Set G) ≤ H ⊓ M :=
  h.toTwoLocalPhaseThree.blockV_facts h.isKGroup.1 h86 hL

theorem nineThree (h : AGLPair p M H R) (h93 : Asc81bNineThree)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : NineThreeConclusion M (pCoreOf 2 H) L :=
  h.toTwoLocalPhaseThree.nineThree h.isKGroup.1 h93 hL

theorem nineThree_not_one (h : AGLPair p M H R) (h85 : Asc81bEightFive) (hD2 : NoXBlockFor G)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ¬ NineThreeOne L ∧ (NineThreeTwo M (pCoreOf 2 H) L →
      ¬ IsSylowTwoOf (barM M (pCoreOf 2 H ⊓ L)) (barM M L)) :=
  h.toTwoLocalPhaseThree.nineThree_not_one h.isKGroup.1 h85 hD2 hL

theorem blockHasThree (h : AGLPair p M H R) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : BlockHasThree M (pCoreOf 2 H) L :=
  h.toTwoLocalPhaseThree.blockHasThree h.isKGroup.1 h85 h86 h93 hD2 hK2 hC3 hK5 hL

end AGLPair

end CFSG.AGLEmbeddingD2
