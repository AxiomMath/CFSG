module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def Ctx7.Fact77 (c : Ctx7 G L) : Prop :=
  IsSylowIn 2 (K7 c.s) (P7 c.e) ∧
  ((∃ L1 : Subgroup G, IsCompPre c.s L1) ∨
    SecProp (K7 c.s) (M3 c.s) (fun Y _ _ _ => Nonempty (Y ≃* SL3Four)))

@[expose] def Ctx7.Fact78 (c : Ctx7 G L) : Prop :=
  ¬ SecProp (K7 c.s) (M3 c.s) (fun Y _ _ _ => Nonempty (Y ≃* SL3Four))

@[expose] def Ctx7.Fact79 (c : Ctx7 G L) : Prop :=
  ∀ L1 : Subgroup G, IsCompPre c.s L1 →
    IsInternalDirect (K7 c.s) ⁅L1, L1⁆ (conjSub c.s.t ⁅L1, L1⁆) ∧
    Nonempty (↥⁅L1, L1⁆ ≃* ↥(centEl (K7 c.s) c.s.t)) ∧ centEl (K7 c.s) c.s.t = JF c.s

@[expose] def Ctx7.Upto77 (c : Ctx7 G L) : Prop := c.Upto76 ∧ c.Fact77

@[expose] def Ctx7.Upto78 (c : Ctx7 G L) : Prop := c.Upto77 ∧ c.Fact78

@[expose] def Ctx7.Upto79 (c : Ctx7 G L) : Prop := c.Upto78 ∧ c.Fact79

@[expose] def Sec77 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto76 → c.Fact77

@[expose] def Sec78 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto77 → c.Fact78

@[expose] def Sec79 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto78 → c.Fact79

@[expose] def Sec7C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto76 → c.Fact77 ∧ c.Fact78 ∧ c.Fact79

theorem sec7C_of (h77 : Sec77) (h78 : Sec78) (h79 : Sec79) : Sec7C := by
  intro G _ _ L hS hL c h5 h6
  have c1 : c.Fact77 := h77 G L hS hL c h5 h6
  have c2 : c.Fact78 := h78 G L hS hL c h5 ⟨h6, c1⟩
  exact ⟨c1, c2, h79 G L hS hL c h5 ⟨⟨h6, c1⟩, c2⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
