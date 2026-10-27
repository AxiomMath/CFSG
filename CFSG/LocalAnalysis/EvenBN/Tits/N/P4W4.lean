module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4W2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section W4

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem Us_fixes_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {u : MulAut ↥d.s56V} (hu : u ∈ Us d) : u (z0V hz) = z0V hz :=
  (fix_Us_iff h49 hd hz h10 h17s.2.1 hz.mem_V).2 (mem_sup_right (mem_zpowers z₀)) u hu

theorem Us_le_W1s (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) :
    Us d ≤ W1s hz := fun u hu =>
  (mem_W1s_iff hz).2 ⟨(le_sup_left : Us d ≤ U0s d).trans
    (node19_W0 h49 hd hz h09 h10 h17s h17 h18).2.2.2.2.1 hu,
    Us_fixes_z0 h49 hd hz h10 h17s hu⟩

theorem W1s_centralizer_x (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h09 : Node09 d z₀)
    (h10 : Node10 d z₀) (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d)
    {a : MulAut ↥d.s56V} (ha : a ∈ W1s hz) (hxa : star d d.x₅ * a = a * star d d.x₅) : a = 1 := by
  obtain ⟨hKcard, hWK, hWst, hW2, hU0W, hWcard, hWcomm, hWsq, hWreg, hWtr⟩ :=
    node19_W0 h49 hd hz h09 h10 h17s h17 h18
  obtain ⟨y₁, hy⟩ := exists_V1_of_node09 h09
  obtain ⟨hF, hCe, hCbot, hCt⟩ := C_data h49 hd hz h10 h17s hy
  have htU : ∀ u ∈ Us d, star d d.t * u = u * star d d.t := fun u hu =>
    hCt u (IsF20.U_le_Pgrp _ _ _ hu)
  have htx : star d d.t * star d d.x₅ = star d d.x₅ * star d d.t :=
    hCt _ (mem_sup_right (mem_sup_left (mem_zpowers _)))
  obtain ⟨haW, haz0⟩ := (mem_W1s_iff hz).1 ha
  have h1 : star d d.t ∈ DeltaS d := by
    rw [h18.2.2.2]
    exact ⟨1, (Us d).one_mem, mul_one _⟩
  have h2 := Ks_conj_DeltaS h49 hd (hWK haW) h1
  rw [h18.2.2.2] at h2
  obtain ⟨u, hu, hau⟩ := h2
  have hau' : star d d.t * u = a * star d d.t * a⁻¹ := hau
  have hxu : star d d.x₅ * u * (star d d.x₅)⁻¹ = u := by
    have hfix : star d d.x₅ * (star d d.t * u) * (star d d.x₅)⁻¹ = star d d.t * u := by
      rw [hau']
      calc star d d.x₅ * (a * star d d.t * a⁻¹) * (star d d.x₅)⁻¹
          = (star d d.x₅ * a) * star d d.t * (star d d.x₅ * a)⁻¹ := by group
        _ = (a * star d d.x₅) * star d d.t * (a * star d d.x₅)⁻¹ := by rw [hxa]
        _ = a * (star d d.x₅ * star d d.t * (star d d.x₅)⁻¹) * a⁻¹ := by group
        _ = a * star d d.t * a⁻¹ := by rw [← htx]; group
    have e : star d d.x₅ * (star d d.t * u) * (star d d.x₅)⁻¹ =
        star d d.t * (star d d.x₅ * u * (star d d.x₅)⁻¹) := by
      calc star d d.x₅ * (star d d.t * u) * (star d d.x₅)⁻¹
          = (star d d.x₅ * star d d.t) * u * (star d d.x₅)⁻¹ := by group
        _ = (star d d.t * star d d.x₅) * u * (star d d.x₅)⁻¹ := by rw [htx]
        _ = star d d.t * (star d d.x₅ * u * (star d d.x₅)⁻¹) := by group
    rw [e] at hfix
    exact mul_left_cancel hfix
  have hu1 : u = 1 := hF.fpf u hu (by
    have := hxu
    rw [mul_inv_eq_iff_eq_mul] at this
    calc star d d.x₅ * u * (star d d.x₅)⁻¹ = u := hxu)
  have hat : a * star d d.t = star d d.t * a := by
    rw [hu1, mul_one] at hau'
    rw [eq_mul_inv_iff_mul_eq] at hau'
    exact hau'.symm
  have haU0 : a ∈ U0s d := hWreg a haW hat
  have htt : star d d.t * star d d.t = 1 := star_t_mul_self h49 hd
  rcases (mem_sup_zpowers_iff_of_comm_invol htt htU).1 haU0 with haU | haU
  ·
    exact hF.fpf a haU (by rw [mul_inv_eq_iff_eq_mul]; exact hxa)
  · exfalso
    have h3 : (star d d.t * a) (z0V hz) = z0V hz := Us_fixes_z0 h49 hd hz h10 h17s haU
    have h4 : star d d.t (a (z0V hz)) = z0V hz := h3
    rw [haz0, star_t_z0 h49 hd hz] at h4
    have : zV h49 hd = 1 := by
      have h5 := congrArg (fun y => y * (z0V hz)⁻¹) h4
      simpa using h5
    exact hd.s56_z_ne_one (congrArg Subtype.val this)

end W4

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
