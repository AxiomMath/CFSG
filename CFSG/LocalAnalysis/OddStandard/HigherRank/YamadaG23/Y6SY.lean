module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SGen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SH2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6_card_Y (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    Nat.card ↥(normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)) =
      2 * Nat.card ↥(normIn c.s.H c.s.fr.A) := by
  set Y : Subgroup G := normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) with hYdef
  have hzt : c.s.fr.z * c.s.t ≠ c.s.t := by
    intro h
    exact y54_z_ne_one (c := c) hH (mul_eq_right.mp h)
  have hY : ∀ y ∈ Y, y * c.s.t * y⁻¹ = c.s.t ∨ y * c.s.t * y⁻¹ = c.s.fr.z * c.s.t :=
    fun y hy => s5_hY_conj c hH hy
  have hy0 : c.d ∈ Y := s5_d_mem_Y c hH
  have hy0t : c.d * c.s.t * c.d⁻¹ = c.s.fr.z * c.s.t := y5_dtd (c := c) hH
  have hmain := y6_card_eq_two_mul_cent (Y := Y) (t := c.s.t) (s := c.s.fr.z * c.s.t)
    hzt hY hy0 hy0t
  have hYH : Y ⊓ centralizer ({c.s.t} : Set G) = normIn c.s.H c.s.fr.A := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxY, hxH⟩ := hx
      exact ⟨hxH, s5_Y_le_NA c hH hxY⟩
    · intro x hx
      obtain ⟨hxH, hxNA⟩ := hx
      exact ⟨s5_NHA_le_Y c hH ⟨hxH, hxNA⟩, hxH⟩
  rw [hYH] at hmain
  rw [hYdef] at hmain
  exact hmain

theorem y6_card_Y_m (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    (c.s.R = c.s.T →
        Nat.card ↥(normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)) =
          18 * Nat.card ↥(C1 c.e)) ∧
      (c.s.R ≠ c.s.T →
        Nat.card ↥(normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G)) =
          36 * Nat.card ↥(C1 c.e)) := by
  have hY := y6_card_Y c hH
  have hNHA := y6_card_NHA hH
  have hC1 : Nat.card ↥(C1 c.e) = 128 := by
    simpa [C1] using y6_card_C1 (c.y6cfg5 hH)
  have hT := y6_card_T hH
  constructor
  · intro hRT
    rw [hY, hNHA, hT.1 hRT, hC1]
  · intro hRT
    rw [hY, hNHA, hT.2 hRT, hC1]

end CFSG.OddStandard.HigherRank.YamadaG23
