module

public import CFSG.GH74.GLS.TwoThin.Rank

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

structure HSetting (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : Assembly.KProper Catalog G
  notCat : ¬ Catalog G
  balanced : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥

theorem HSetting.isKProperSimple {G : Type} [Group G] [Finite G] (h : HSetting G) :
    GH74.GLS.IsKProperSimple G :=
  ⟨h.simple, h.nonab, h.kProper⟩

theorem HSetting.rank_centralizer {G : Type} [Group G] [Finite G] (h : HSetting G)
    (h3 : 3 ≤ CFSG.pRank 2 G) {y : G} (hy : orderOf y = 2) :
    3 ≤ CFSG.pRank 2 ↥(centralizer ({y} : Set G)) :=
  GH74.GLS.TwoThin.rankThreeCentralizers G h.simple h.nonab h3 y hy

end CFSG.OddStandard.SmallF3.HypA2
