module

public import CFSG.GH74.GLS.TwoThin.Terminal
public import CFSG.GH74.GLS.TwoThin.Closure
public import CFSG.GH74.GLS.TwoThin.Rank
public import CFSG.GH74.GLS.TwoThin.KGroupCore

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup

theorem s_twoThinOfB2P_of_kgroup {PG Q : GroupPred}
    (hQ : ∀ (G : Type) [Group G] [Finite G], PG G → ∀ x : G, orderOf x = 2 →
      Q (barQ ↥(centralizer ({x} : Set G))))
    (hKG : TwoThinKGroupFactQ Q) : S_twoThinOfB2P PG :=
  s_twoThinOfB2P_of_reduction rankThreeCentralizers
    (fun _ _ _ hPG hG _ hno =>
      b2PumpupClosed_of_kgroupQ (hQ _ hPG) (l2Sub_of_not_l2Meets_g2 hG hno) hKG)
    terminalExists

theorem s_twoThinOfB2P_of_core {PG Q P : GroupPred}
    (hQ : ∀ (G : Type) [Group G] [Finite G], PG G → ∀ x : G, orderOf x = 2 →
      Q (barQ ↥(centralizer ({x} : Set G))))
    (hQP : ∀ (H : Type) [Group H] [Finite H], Q H → ∀ L : Subgroup H, P ↥L)
    (hKG : TwoThinKGroupCoreP P) : S_twoThinOfB2P PG :=
  s_twoThinOfB2P_of_kgroup hQ (twoThinKGroupFactQ_of_coreP hQP hKG)

end CFSG.GH74.GLS.TwoThin
