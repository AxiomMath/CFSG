module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure F33Hyp (s : Setting3 G L) (e : Setting3.Ext s) : Prop where
  hS : HRSetting G L
  hZ : Odd (Nat.card ↥(center ↥L))
  hOut : (innerAut (L ⧸ center L)).index = 2
  h31 : s.Fact31
  hDef : e.FactDef
  h32 : e.Fact32
  hLF : LFacts s

abbrev f3P (s : Setting3 G L) : Subgroup G := s.fr.B ⊔ zpowers s.t

abbrev f3N (s : Setting3 G L) : Subgroup G := normIn s.H s.fr.B

abbrev f3Y (s : Setting3 G L) : Subgroup G := centIn s.X (cen s.fr.B)

abbrev f3X0 (s : Setting3 G L) : Subgroup G := centIn s.H (cen s.fr.B)

abbrev f3Y1 (s : Setting3 G L) : Subgroup G := ⁅f3Y s, f3N s⁆ ⊔ f3P s

theorem f3_C₂_eq (s : Setting3 G L) : s.C₂ = pCoreOf 2 (f3Y1 s) := rfl

abbrev f3phi (s : Setting3 G L) (y : G) : G := y * s.t * y⁻¹ * s.t⁻¹

structure ExtCtx {G : Type} [Group G] (P X₀ Y N : Subgroup G) : Prop where
  P_le : P ≤ X₀
  X₀_le : X₀ ≤ Y
  Y_N : ∀ n ∈ N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y
  P_Y : ∀ y ∈ Y, ∀ p ∈ P, y * p * y⁻¹ ∈ P
  P_N : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P
  X₀_Y : ∀ y ∈ Y, ∀ a ∈ X₀, y * a * y⁻¹ ∈ X₀
  X₀_N : ∀ n ∈ N, ∀ a ∈ X₀, n * a * n⁻¹ ∈ X₀
  cosets : ∀ a ∈ X₀, ∀ b ∈ X₀, a ∈ P ∨ b ∈ P ∨ a⁻¹ * b ∈ P

theorem f3_oddH_eq_bot (hS : HRSetting G L) (s : Setting3 G L) : s.oddH = ⊥ := by
  show (CFSG.oddCore ↥(centralizer ({s.t} : Set G))).map
      (centralizer ({s.t} : Set G)).subtype = ⊥
  rw [hS.balanced s.t s.t_order, Subgroup.map_bot]

end CFSG.OddStandard.HigherRank.YamadaG23
