module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def Ctx7.Fact71 (c : Ctx7 G L) : Prop :=
  (normalizer (C0 c.e : Set G) = normIn c.s.H c.s.fr.A ⊔ zpowers c.d ∧
    normalizer (C0 c.e : Set G) ≤ normalizer (V1 c.e : Set G)) ∧
  (normalizer (C1 c.e : Set G) = normIn c.s.H c.s.fr.A ⊔ M6 c.e ∧
    c.s.H ⊓ M6 c.e = c.s.fr.A ∧
    ActsTransOutside (M6 c.e) (C1 c.e) (V1 c.e) (AV1 c.e) ∧
    ⁅M6 c.e, AV1 c.e⁆ ≤ V1 c.e ∧
    QuotModIso (normIn c.s.H c.s.fr.A) (M6 c.e) (AV1 c.e) c.s.fr.A c.s.fr.Z) ∧
  (C6 c.e = M6 c.e ⊔ zpowers c.s.t ∧ M3 c.s ≤ M6 c.e ∧ M4 c.e ≤ M6 c.e)

@[expose] def Ctx7.Fact72 (c : Ctx7 G L) : Prop :=
  (M2 c.s = c.s.fr.B ⊔ V2 c.e ∧ (∀ b ∈ c.s.fr.B, ∀ v ∈ V2 c.e, b * v = v * b) ∧
    c.s.fr.B ⊓ V2 c.e = cen c.s.fr.B ∧ Nat.card (V2 c.e) = 2 ^ 4 ∧
    ∀ x ∈ c.s.fr.S, ∀ v ∈ V1 c.e, x * v = v * x) ∧
  IsElemAbelian 2 (M4 c.e) ∧
  (⁅M6 c.e, M6 c.e⁆ = V1 c.e ∧
    SecProp (M6 c.e) (V1 c.e) (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y))) ∧
  (c.s.R ≠ c.s.T → ∀ m ∈ M6 c.e, ⁅c.g, m⁆ ∈ M3 c.s)

@[expose] def Ctx7.Fact73 (c : Ctx7 G L) : Prop :=
  normalizer (C6 c.e : Set G) = normIn c.s.H c.s.fr.A ⊔ M6 c.e

@[expose] def Ctx7.Fact74 (c : Ctx7 G L) : Prop :=
  IsSylowIn 2 (centralizerSection c.s.fr.A c.s.fr.Z) (C1 c.e) ∧
  IsSylowIn 2 (centralizerSection (AV1 c.e) (V1 c.e)) (C6 c.e)

@[expose] def Ctx7.Upto71 (c : Ctx7 G L) : Prop := c.Fact71

@[expose] def Ctx7.Upto72 (c : Ctx7 G L) : Prop := c.Upto71 ∧ c.Fact72

@[expose] def Ctx7.Upto73 (c : Ctx7 G L) : Prop := c.Upto72 ∧ c.Fact73

@[expose] def Ctx7.Upto74 (c : Ctx7 G L) : Prop := c.Upto73 ∧ c.Fact74

@[expose] def Sec71 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Fact71

@[expose] def Sec72 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto71 → c.Fact72

@[expose] def Sec73 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto72 → c.Fact73

@[expose] def Sec74 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto73 → c.Fact74

@[expose] def Sec7A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto74

theorem sec7A_of (h71 : Sec71) (h72 : Sec72) (h73 : Sec73) (h74 : Sec74) : Sec7A := by
  intro G _ _ L hS hL c h5
  have a1 : c.Upto71 := h71 G L hS hL c h5
  have a2 : c.Upto72 := ⟨a1, h72 G L hS hL c h5 a1⟩
  have a3 : c.Upto73 := ⟨a2, h73 G L hS hL c h5 a2⟩
  exact ⟨a3, h74 G L hS hL c h5 a3⟩

end CFSG.OddStandard.HigherRank.YamadaG23
