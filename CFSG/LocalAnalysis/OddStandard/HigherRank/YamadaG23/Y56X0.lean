module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Cosets
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Nrm

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y56_X0_cosets {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ e4X0 s, ∀ b ∈ e4X0 s, a ∈ e4Q s ∨ b ∈ e4Q s ∨ a⁻¹ * b ∈ e4Q s := by
  have h := y5_cent_cosets hH (V := s.fr.E) (y56_E_le_L s)
  rw [y56_centIn_L_E hH] at h
  exact h

theorem y56_X0_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ e4X0 s, x ^ 2 ∈ e4Q s := by
  intro x hx
  rcases y56_X0_cosets hH x⁻¹ (Subgroup.inv_mem (e4X0 s) hx) x hx with h | h | h
  · simpa only [inv_inv, pow_two] using
      Subgroup.mul_mem (e4Q s) (Subgroup.inv_mem (e4Q s) h) (Subgroup.inv_mem (e4Q s) h)
  · simpa only [pow_two] using Subgroup.mul_mem (e4Q s) h h
  · simpa only [inv_inv, pow_two] using h

theorem y56_Y_X0_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ y ∈ e4Y s, ∀ x ∈ e4X0 s, ⁅y, x⁆ ∈ e4Q s := by
  intro y hy x hx
  by_cases hxQ : x ∈ e4Q s
  · have hyxQ : y * x * y⁻¹ ∈ e4Q s := y56_Y_norm_Q hH y hy x hxQ
    have hxinvQ : x⁻¹ ∈ e4Q s := Subgroup.inv_mem (e4Q s) hxQ
    rw [commutatorElement_def]
    exact Subgroup.mul_mem (e4Q s) hyxQ hxinvQ
  · have hx'X0 : y * x * y⁻¹ ∈ e4X0 s := y56_Y_norm_X0 hH y hy x hx
    have hx'Q : y * x * y⁻¹ ∉ e4Q s := by
      intro h
      have h' : y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ ∈ e4Q s :=
        y56_Y_norm_Q hH y⁻¹ (Subgroup.inv_mem (e4Y s) hy) _ h
      have heq : y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x := by group
      rw [heq] at h'
      exact hxQ h'
    rcases y56_X0_cosets hH x hx (y * x * y⁻¹) hx'X0 with h | h | h
    · exact absurd h hxQ
    · exact absurd h hx'Q
    · have hconj : x * (x⁻¹ * (y * x * y⁻¹)) * x⁻¹ ∈ e4Q s :=
        y56_Y_norm_Q hH x (y56_X0_le_Y hH hx) _ h
      have heq : x * (x⁻¹ * (y * x * y⁻¹)) * x⁻¹ = (y * x * y⁻¹) * x⁻¹ := by group
      rw [heq] at hconj
      rw [commutatorElement_def]
      exact hconj

end CFSG.OddStandard.HigherRank.YamadaG23
