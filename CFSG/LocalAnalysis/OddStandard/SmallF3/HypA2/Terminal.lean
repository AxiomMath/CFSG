module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaC

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem inS_of_longPumpUp (hC : ClosureLeaves) {G : Type} [Group G] [Finite G] (hG : HSetting G)
    {x x' : G} {K K' : Subgroup G} (h : GH74.GLS.LongPumpUp 2 x K x' K')
    (hK : InS (↥K ⧸ center ↥K)) : InS (↥K' ⧸ center ↥K') := by
  have key : ∀ q : G × Subgroup G,
      Relation.ReflTransGen
        (fun a b : G × Subgroup G => GH74.GLS.PumpUpLT 2 a.1 a.2 b.1 b.2) (x, K) q →
      InS (↥q.2 ⧸ center ↥q.2) := by
    intro q hq
    induction hq with
    | refl => exact hK
    | @tail b c hab hbc ih =>
        rcases b with ⟨a, B⟩
        rcases c with ⟨a', B'⟩
        exact (inS_of_pumpUpLT hC hG hbc ih).1
  exact key (x', K') h.2

theorem exists_twoTerminal_inS (hC : ClosureLeaves) (hb : GH74.GLS.B_ig_6_10) {G : Type}
    [Group G] [Finite G] (hG : HSetting G) (h3 : 3 ≤ CFSG.pRank 2 G) {y : G} {K : Subgroup G}
    (hI : GH74.GLS.IsILo 2 y K) (hK : InS (↥K ⧸ center ↥K)) :
    ∃ (x' : G) (K' : Subgroup G), GH74.GLS.IsTwoTerminal x' K' ∧ InS (↥K' ⧸ center ↥K') := by
  obtain ⟨x', K', hlong, hterm⟩ := hb G hG.isKProperSimple h3 y K hI
  exact ⟨x', K', hterm, inS_of_longPumpUp hC hG hlong hK⟩

end CFSG.OddStandard.SmallF3.HypA2
