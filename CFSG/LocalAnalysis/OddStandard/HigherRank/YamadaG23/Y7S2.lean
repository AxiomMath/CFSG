module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def Ctx7.Fact75 (c : Ctx7 G L) : Prop :=
  (normalizer ((c.s.fr.B ⊔ C3 c.s : Subgroup G) : Set G) ⊓ normalizer (M3 c.s : Set G) =
      normIn c.s.H c.s.fr.B ⊔ M7 c.s ∧
    c.s.H ⊓ M7 c.s = c.s.fr.B ∧
    ActsTransOutside (M7 c.s) (c.s.fr.B ⊔ C3 c.s) (M3 c.s) (c.s.fr.B ⊔ M3 c.s) ∧
    QuotModIso (normIn c.s.H c.s.fr.B) (M7 c.s) (c.s.fr.B ⊔ M3 c.s) c.s.fr.B c.s.fr.F) ∧
  (C7 c.s = M7 c.s ⊔ zpowers c.s.t ∧ M4 c.e ≤ M7 c.s ∧ V2 c.e ≤ cen (M7 c.s)) ∧
  SecProp (M7 c.s) (M3 c.s) (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y)) ∧
  (c.s.R ≠ c.s.T → ∀ m ∈ M7 c.s, ⁅c.g, m⁆ ∈ M3 c.s)

@[expose] def Ctx7.Fact76 (c : Ctx7 G L) : Prop :=
  (P7 c.e : Set G) = (M6 c.e : Set G) * (M7 c.s : Set G) ∧
  Nat.card (P7 c.e) = 2 ^ 12 ∧ centEl (P7 c.e) c.s.t = c.s.fr.S ∧
  P7 c.e ≤ normalizer (M6 c.e : Set G)

@[expose] def Ctx7.Upto75 (c : Ctx7 G L) : Prop := c.Upto74 ∧ c.Fact75

@[expose] def Ctx7.Upto76 (c : Ctx7 G L) : Prop := c.Upto75 ∧ c.Fact76

@[expose] def Sec75 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto74 → c.Fact75

@[expose] def Sec76 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto75 → c.Fact76

@[expose] def Sec7B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto74 → c.Fact75 ∧ c.Fact76

theorem sec7B_of (h75 : Sec75) (h76 : Sec76) : Sec7B := by
  intro G _ _ L hS hL c h5 h4
  have b1 : c.Fact75 := h75 G L hS hL c h5 h4
  exact ⟨b1, h76 G L hS hL c h5 ⟨h4, b1⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
