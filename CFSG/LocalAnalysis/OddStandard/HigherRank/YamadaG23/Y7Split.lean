module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Final

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def Sec7SylowRT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.s.R = c.s.T →
      ∃ Q N : Subgroup G, IsSylowIn 2 ⊤ Q ∧ N ≤ Q ∧
        SecProp Q N (fun Y _ _ _ => IsCyclic Y) ∧ ∀ x : G, IsExtremalConj Q c.s.t x → x ∉ N

@[expose] def Sec7SylowNT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.s.R ≠ c.s.T →
      ∃ Q N : Subgroup G, IsSylowIn 2 ⊤ Q ∧ N ≤ Q ∧
        SecProp Q N (fun Y _ _ _ => IsCyclic Y) ∧ ∀ x : G, IsExtremalConj Q c.s.t x → x ∉ N

theorem sec7Sylow_of_split (hRT : Sec7SylowRT) (hNT : Sec7SylowNT) : Sec7Sylow := by
  intro G _ _ L hS hL c hc
  by_cases h : c.s.R = c.s.T
  · exact hRT G L hS hL c hc h
  · exact hNT G L hS hL c hc h

theorem sec7False_of_split (hRT : Sec7SylowRT) (hNT : Sec7SylowNT) : Sec7False :=
  sec7False_of_sylow (sec7Sylow_of_split hRT hNT)

end CFSG.OddStandard.HigherRank.YamadaG23
