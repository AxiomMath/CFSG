module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPureTwo
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem AGLPair.false_of_one_weakSBlock_of_autRank (h : AGLPair 3 M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hH : Open.pRank 3 H = 2) (hM4 : 4 ≤ Open.pRank 3 M)
    (hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hk1 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L)
    (hrank : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      IsElemAbelian 3 E →
      Open.pRank 3 E ≤ Open.pRank 3 (E ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2)
    (hy : ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : False :=
  h.false_of_one_weakSBlock_of_rank h84 h86 hD2 hH hM4 hthree hL hk1
    (fun E hEN _ hEbel => hrank E hEN hEbel) hy

end CFSG.AGLEmbeddingD2

