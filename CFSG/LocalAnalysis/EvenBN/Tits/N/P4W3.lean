module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4W2
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Lay
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Cnt
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Sub

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section W3

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem star_x5_normalizes_W1s (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h09 : Node09 d z₀) (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀)
    (h18 : Node18 d) : ∀ p ∈ W1s hz, star d d.x₅ * p * (star d d.x₅)⁻¹ ∈ W1s hz := by
  obtain ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩ :=
    node19_W0 h49 hd hz h09 h10 h17s h17 h18
  have hxK : star d d.x₅ ∈ Ks d := star_x5_mem_Ks h49 hd
  intro p hp
  obtain ⟨hpW, hpz⟩ := (mem_W1s_iff hz).1 hp
  refine (mem_W1s_iff hz).2 ⟨hWst _ hxK p hpW, ?_⟩
  have hx0 := star_x5_fixes_z0 h49 hd hz
  have hx1 : (star d d.x₅)⁻¹ (z0V hz) = z0V hz := by
    have := congrArg (fun y => (star d d.x₅)⁻¹ y) hx0
    simpa using this.symm
  show star d d.x₅ (p ((star d d.x₅)⁻¹ (z0V hz))) = z0V hz
  rw [hx1, hpz, hx0]

theorem W1s_elemAb (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    (∀ w ∈ W1s hz, ∀ w' ∈ W1s hz, w * w' = w' * w) ∧ ∀ w ∈ W1s hz, w * w = 1 := by
  obtain ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩ :=
    node19_W0 h49 hd hz h09 h10 h17s h17 h18
  obtain ⟨y₁, hy⟩ := exists_V1_of_node09 h09
  obtain ⟨hF, hCe, hCbot, hCt⟩ := C_data h49 hd hz h10 h17s hy
  have hzz : d.z * d.z = 1 := hd.s56_z_sq
  have hz₀z₀ : z₀ * z₀ = 1 := h10.sq_V hz.mem_V
  have hzz₀ : d.z * z₀ = z₀ * d.z := (hz.cen hd.s56_z_mem_E).symm
  have htU : ∀ u ∈ Us d, star d d.t * u = u * star d d.t := fun u hu =>
    hCt u (IsF20.U_le_Pgrp _ _ _ hu)
  have htt : star d d.t * star d d.t = 1 := star_t_mul_self h49 hd
  have hxK : star d d.x₅ ∈ Ks d := star_x5_mem_Ks h49 hd
  have htW : star d d.t ∈ W0s d := hU0W (mem_sup_right (mem_zpowers _))
  have hcommV : ∀ a b : ↥d.s56V, a * b = b * a := fun a b => Subtype.ext (h10.comm_V a.2 b.2)
  have hsqV : ∀ a : ↥d.s56V, a * a = 1 := fun a => Subtype.ext (h10.sq_V a.2)
  have hW1K : W1s hz ≤ Ks d := (W1s_le_W0s hz).trans hWK
  have hxP := star_x5_normalizes_W1s h49 hd hz h09 h10 h17s h17 h18
  have hWZ : ∀ w ∈ W1s hz, ∀ ζ ∈ Zzs d z₀, w ζ = ζ := by
    intro w hw ζ hζ
    obtain ⟨hwW, hwz0⟩ := (mem_W1s_iff hz).1 hw
    have hwz : w (zV h49 hd) = zV h49 hd := Ks_fixes_z h49 hd hz h10 h17 (hWK hwW)
    have hmem : (ζ : G) ∈ zpowers d.z ⊔ zpowers z₀ := hζ
    rcases (CFSG.LocalAnalysis.EvenBN.Tits.N.mem_sup_zpowers_iff hzz hz₀z₀ hzz₀ _).1 hmem with
      h | h | h | h
    · have h1 : ζ = 1 := Subtype.ext h
      rw [h1, map_one]
    · have h1 : ζ = zV h49 hd := Subtype.ext h
      rw [h1]
      exact hwz
    · have h1 : ζ = z0V hz := Subtype.ext h
      rw [h1]
      exact hwz0
    · have h1 : ζ = zV h49 hd * z0V hz := Subtype.ext h
      rw [h1, map_mul, hwz, hwz0]
  have hlay := layers_trivial hcommV (Zzs_le_E0s hd) (card_Zzs h49 hd hz h10) (card_E0s h49 hd hz h10)
    (card_V' h10) (x := star d d.x₅) (star_x5_pow_five h49 hd)
    (Ks_Zzs_iff h49 hd hz h10 h17 h18 hxK) (Ks_E0s_iff h49 hd hz h10 h17 hxK)
    (star_x5_fix_Zzs h49 hd hz h10) (P := W1s hz) (hW2.to_le (W1s_le_W0s hz)) hxP
    (fun p hp => Ks_Zzs_iff h49 hd hz h10 h17 h18 (hW1K hp))
    (fun p hp => Ks_E0s_iff h49 hd hz h10 h17 (hW1K hp))
  have hPU : W0s d ≤ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) :=
    fun w hw => Ks_le_normalizer_Us h49 hd h18 (hWK hw)
  have hWU : ∀ w ∈ W1s hz, ∀ u ∈ Us d, w * u = u * w := fun w hw u hu =>
    IsF20.centralizes_of_isPGroup_two hF hW2 hPU (fun p hp => hWst _ hxK p hp) w
      (W1s_le_W0s hz hw) u hu
  have hreg : ∀ u ∈ Us d, ∃ w ∈ W1s hz, w * star d d.t * w⁻¹ * (star d d.t)⁻¹ = u := by
    intro u hu
    obtain ⟨w', hw', hw't⟩ := hWtr u hu
    have hcomm1 : star d d.t * u * (star d d.t)⁻¹ = u := by
      calc star d d.t * u * (star d d.t)⁻¹ = u * star d d.t * (star d d.t)⁻¹ := by rw [htU u hu]
        _ = u := by group
    rcases Ks_z0_cases h49 hd hz h10 h17 h18 (hWK hw') with h | h
    · refine ⟨w', (mem_W1s_iff hz).2 ⟨hw', h⟩, ?_⟩
      rw [hw't, hcomm1]
    · refine ⟨w' * star d d.t, (mem_W1s_iff hz).2 ⟨mul_mem hw' htW, ?_⟩, ?_⟩
      · show w' (star d d.t (z0V hz)) = z0V hz
        rw [star_t_z0 h49 hd hz, map_mul, Ks_fixes_z h49 hd hz h10 h17 (hWK hw'), h]
        have : zV h49 hd * zV h49 hd = 1 := Subtype.ext hzz
        rw [← mul_assoc, this, one_mul]
      · have e : w' * star d d.t * star d d.t * (w' * star d d.t)⁻¹ * (star d d.t)⁻¹ =
            w' * star d d.t * w'⁻¹ * (star d d.t)⁻¹ := by group
        rw [e, hw't, hcomm1]
  have hC : ∀ l : ↥d.s56V, (∀ u ∈ Us d, u l = l) → l ∈ Zzs d z₀ := fun l hl =>
    (fix_Us_iff h49 hd hz h10 h17s.2.1 l.2).1 hl
  have := elemAb_of_layers hcommV hsqV (Zzs_le_E0s hd) hWZ (fun w hw => (hlay w hw).1)
    (fun w hw => (hlay w hw).2) (star_t_mem_trivOn_flag h49 hd hz h10) (star_t_mem_trivOn_top h49 hd)
    hWU hreg hC
  exact ⟨this.2.1, this.2.2⟩

end W3

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
