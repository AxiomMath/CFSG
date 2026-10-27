module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec4S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec7S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def Sec7Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 →
      ∃ Q N : Subgroup G, IsSylowIn 2 ⊤ Q ∧ N ≤ Q ∧
        SecProp Q N (fun Y _ _ _ => IsCyclic Y) ∧ ∀ x : G, IsExtremalConj Q c.s.t x → x ∉ N

theorem sec7False_of_sylow (h : Sec7Sylow) : Sec7False := by
  intro G _ _ L hS hL c hc
  haveI : IsSimpleGroup G := hS.std.simple
  obtain ⟨Q, N, hsyl, hNle, hsec, hext⟩ := h G L hS hL c hc
  exact transfer_of_isSylowIn hS.std.nonab hsyl hNle hsec c.s.t_order hext

end CFSG.OddStandard.HigherRank.YamadaG23
