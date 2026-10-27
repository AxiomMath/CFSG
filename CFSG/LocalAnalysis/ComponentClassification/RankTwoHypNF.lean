module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ComponentClassification.RankTwoStandard

open CFSG.Open

structure RankTwoHypNF (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop where
  standard : standardComponentIsStandard A
  not_normal : ¬ A.Normal
  rank : 2 ≤ pRank 2 (Subgroup.centralizer (A : Set G))

theorem RankTwoHyp.toNF {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (h : RankTwoHyp G A) : RankTwoHypNF G A :=
  ⟨h.standard, h.not_normal, h.rank⟩

theorem RankTwoHypNF.ofKProper {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (h : RankTwoHypNF G A) (hk : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) :
    RankTwoHyp G A :=
  ⟨hk, h.standard, h.not_normal, h.rank⟩

end CFSG.ComponentClassification.RankTwoStandard
