module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaW
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P10Y
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N5

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.kappaAhat_exists_x (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz : d.S56Z0 z₀) (hκ : ¬ d.S56KappaBit) :
    ∃ x ∈ d.s56V, d.s56Eps x = d.pv 10 ∧ x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.pv 11 := by
  obtain ⟨x₀, hx₀V, hx₀ε⟩ := hd.s56_V_eps_surj h49 hz (d.pv 10) hd.s56_pv10_mem_E
  rcases hd.kappaT_comm_pv7 h49 hz hκ hx₀V hx₀ε with h | h
  · exact ⟨x₀, hx₀V, hx₀ε, h⟩
  · have h8E : d.pv 8 ∈ d.E := s56_pv8_mem_E d
    have h8V : d.pv 8 ∈ d.s56V := hd.s56_E_le_V h49 h8E
    have hz2 : d.z * d.z = 1 := hd.s56_E_sq hd.s56_z_mem_E
    refine ⟨x₀ * d.pv 8, mul_mem hx₀V h8V, ?_, ?_⟩
    · rw [hd.s56_eps_mul_Q2' hx₀V.2 h8V.2, hx₀ε, (hd.s56_V_eps_eq_one_iff h49 h8V).2 h8E,
        mul_one]
    · have hmul := hd.kTau_mul h49 hz hx₀V h8V
      have h8 : d.kTau (d.pv 8) = d.z := hd.s56_pv8_comm_pv7
      unfold kTau at hmul h8
      rw [hmul, h, h8, mul_assoc, hz2, mul_one]

theorem Hyp.kappaAhat_sq (h49 : d.Thm49Statement) (hd : d.Hyp) (hR : d.ρ.range = ⊤) {z₀ : G}
    (hz : d.S56Z0 z₀) (hsq : z₀ * z₀ = 1) {x : G} (hxV : x ∈ d.s56V)
    (hxε : d.s56Eps x = d.pv 10) (hτ : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.pv 11) :
    x * x = d.z := by
  obtain ⟨y, hy, hyT, hyz⟩ := N.p09_exists_y5 h49 hd hz hR
  have hy2 : y * y = d.z := N.P2b.y_sq hd hz hy hyT hyz (N.p09_t_not_mem hd hz)
  have hyx : y * x = x * y := N.node10_y_comm_V h49 hd hz hy hyz x hxV
  have hyt : y * d.t = d.t * y := N.node10_y_comm_t hd hy
  have hy7 : y * d.pv 7 * y⁻¹ = d.pv 7 * d.pv 11 := N.node10_y_conj_pv7 hd hy
  have hv11E : d.pv 11 ∈ d.E := s56_pv11_mem_E d
  have hv11F : d.pv 11 ∈ d.F := s56_pv11_mem_F d
  have hv7F : d.pv 7 ∈ d.F := hd.s56_pv7_mem_F
  have hx11 : x * d.pv 11 = d.pv 11 * x := s56_V_comm_E hxV hv11E
  have hx7 : x * d.pv 7 * x⁻¹ = d.pv 11 * d.pv 7 := by
    rw [← hτ]; group
  have h711 : d.pv 7 * d.pv 11 = d.pv 11 * d.pv 7 := hd.s56_F_comm hv7F hv11F
  have h1111 : d.pv 11 * d.pv 11 = 1 := hd.s56_E_sq hv11E
  have hwE : ∀ e ∈ d.E, x * y * e = e * (x * y) := by
    intro e he
    have h1 : y * e = e * y := N.node10_y_comm_E hd hy he
    have h2 : x * e = e * x := s56_V_comm_E hxV he
    calc x * y * e = x * (y * e) := by group
      _ = x * (e * y) := by rw [h1]
      _ = (x * e) * y := by group
      _ = (e * x) * y := by rw [h2]
      _ = e * (x * y) := by group
  have hw7 : x * y * d.pv 7 * (x * y)⁻¹ = d.pv 7 := by
    calc x * y * d.pv 7 * (x * y)⁻¹ = x * (y * d.pv 7 * y⁻¹) * x⁻¹ := by group
      _ = x * (d.pv 7 * d.pv 11) * x⁻¹ := by rw [hy7]
      _ = (x * d.pv 7 * x⁻¹) * (x * d.pv 11 * x⁻¹) := by group
      _ = (d.pv 11 * d.pv 7) * d.pv 11 := by
          rw [hx7, show x * d.pv 11 * x⁻¹ = d.pv 11 by rw [hx11]; group]
      _ = d.pv 7 * (d.pv 11 * d.pv 11) := by rw [← h711]; group
      _ = d.pv 7 := by rw [h1111, mul_one]
  have hwF : ∀ f ∈ d.F, x * y * f = f * (x * y) := by
    intro f hf
    rcases Hyp.s56_F_cases d hf with h | h
    · exact hwE f h
    · have h7f := hwE _ h
      have h7c : x * y * d.pv 7 = d.pv 7 * (x * y) := by
        calc x * y * d.pv 7 = (x * y * d.pv 7 * (x * y)⁻¹) * (x * y) := by group
          _ = d.pv 7 * (x * y) := by rw [hw7]
      have hf' : f = (d.pv 7)⁻¹ * (d.pv 7 * f) := by group
      rw [hf']
      calc x * y * ((d.pv 7)⁻¹ * (d.pv 7 * f))
          = (x * y * (d.pv 7)⁻¹) * (d.pv 7 * f) := by group
        _ = ((d.pv 7)⁻¹ * (x * y)) * (d.pv 7 * f) := by
            congr 1
            calc x * y * (d.pv 7)⁻¹ = (d.pv 7)⁻¹ * (d.pv 7 * (x * y)) * (d.pv 7)⁻¹ := by group
              _ = (d.pv 7)⁻¹ * (x * y * d.pv 7) * (d.pv 7)⁻¹ := by rw [h7c]
              _ = (d.pv 7)⁻¹ * (x * y) := by group
        _ = (d.pv 7)⁻¹ * (x * y * (d.pv 7 * f)) := by group
        _ = (d.pv 7)⁻¹ * ((d.pv 7 * f) * (x * y)) := by rw [h7f]
        _ = (d.pv 7)⁻¹ * (d.pv 7 * f) * (x * y) := by group
  have hwt : x * y * d.t * (x * y)⁻¹ = d.t * d.pv 10 := by
    calc x * y * d.t * (x * y)⁻¹ = x * (y * d.t) * y⁻¹ * x⁻¹ := by group
      _ = x * (d.t * y) * y⁻¹ * x⁻¹ := by rw [hyt]
      _ = x * d.t * x⁻¹ := by group
      _ = d.t * d.s56Eps x := hd.s56_conj_t x
      _ = d.t * d.pv 10 := by rw [hxε]
  have hw2 : x * y * (x * y) = x * x * d.z := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hyx]
      _ = x * x * (y * y) := by group
      _ = x * x * d.z := by rw [hy2]
  have hx1 : x * x ≠ 1 := fun h1 =>
    hd.kappaW h49 hwF hwt (by rw [hw2, h1, one_mul])
  rcases hd.zpowers_z_cases (hd.s56_V_sq_mem_of_sq_eq_one h49 hz hsq hxV) with h | h
  · exact absurd h hx1
  · exact h

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
