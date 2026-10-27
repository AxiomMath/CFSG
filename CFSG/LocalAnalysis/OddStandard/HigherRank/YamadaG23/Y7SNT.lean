module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Top

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def U7 (c : Ctx7 G L) (L1 : Subgroup G) : Subgroup G := ⁅L1, L1⁆ ⊓ P7 c.e

@[expose] def U07 (c : Ctx7 G L) (L1 P1 : Subgroup G) : Subgroup G :=
  conjSub c.s.t (centIn P1 ⁅L1, L1⁆)

structure NTCfg (c : Ctx7 G L) (L1 P1 P0 : Subgroup G) : Prop where
  comp : IsCompPre c.s L1
  syl : IsSylowIn 2 (normalizer (K7 c.s : Set G)) P1
  le : P7 c.e ⊔ closure {c.g, c.s.t} ≤ P1
  p0 : P0 = normIn P1 ⁅L1, L1⁆
  normal : P1 ≤ normalizer (P0 : Set G)
  split : P1 = P0 ⊔ zpowers c.s.t
  cases :
    (∃ g0 : G, g0 ∈ U07 c L1 P1 ∧ g0 ^ 2 = 1 ∧ g0 ∉ U7 c L1 ∧
        U07 c L1 P1 = U7 c L1 ⊔ zpowers g0 ∧ g0 * (c.s.t * g0 * c.s.t⁻¹) = c.g ∧
        IsInternalDirect P0 (U07 c L1 P1) (conjSub c.s.t (U07 c L1 P1)) ∧
        Nonempty (↥(U07 c L1 P1) ≃* ↥(c.s.fr.S ⊔ zpowers c.g))) ∨
    (U07 c L1 P1 = U7 c L1 ∧ P0 = P7 c.e ⊔ zpowers c.g)

@[expose] def Sec7NT1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto79 → c.s.R ≠ c.s.T →
      ∃ L1 P1 P0 : Subgroup G, NTCfg c L1 P1 P0

@[expose] def Sec7NT2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto79 → c.s.R ≠ c.s.T →
      ∀ L1 P1 P0 : Subgroup G, NTCfg c L1 P1 P0 → IsSylowIn 2 ⊤ P1

@[expose] def Sec7NT3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.Upto79 → c.s.R ≠ c.s.T →
      ∀ L1 P1 P0 : Subgroup G, NTCfg c L1 P1 P0 → IsSylowIn 2 ⊤ P1 →
        ∀ x : G, IsConj c.s.t x → x ∉ P0

theorem sec7NT_of (h1 : Sec7NT1) (h2 : Sec7NT2) (h3 : Sec7NT3) : Sec7NT := by
  intro G _ _ L hS hL c h5 h7 hRT
  obtain ⟨L1, P1, P0, hcfg⟩ := h1 G L hS hL c h5 h7 hRT
  have hsyl := h2 G L hS hL c h5 h7 hRT L1 P1 P0 hcfg
  exact ⟨P1, P0, hsyl, hcfg.p0 ▸ inf_le_left, hcfg.normal, hcfg.split,
    h3 G L hS hL c h5 h7 hRT L1 P1 P0 hcfg hsyl⟩

end CFSG.OddStandard.HigherRank.YamadaG23
