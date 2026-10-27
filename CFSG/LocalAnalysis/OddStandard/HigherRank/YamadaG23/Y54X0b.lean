module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54D
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54X0a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y54_t_sq (s : Setting3 G L) : s.t ^ 2 = 1 := by
  simpa [s.t_order] using pow_orderOf_eq_one s.t

private theorem y54_gg_eq_one {g : G} (hg2 : g ^ 2 = 1) : g * g = 1 := by
  rw [← pow_two]; exact hg2

private theorem y54_ft_mul {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {f f' : G}
    (hf : f ∈ s.fr.F) (hf' : f' ∈ s.fr.F) :
    (f * s.t) * (f' * s.t) = (f * f') * (s.t * s.t) := by
  have h : s.t * f' = f' * s.t := (y54_t_comm_F s f' hf').symm
  calc (f * s.t) * (f' * s.t) = f * (s.t * f') * s.t := by group
    _ = f * (f' * s.t) * s.t := by rw [h]
    _ = (f * f') * (s.t * s.t) := by group

private theorem y54_P_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ p ∈ f4P s, p ^ 2 = 1 := by
  intro p hp
  obtain hpF | ⟨f, hf, rfl⟩ := y54_mem_P s hp
  · exact y54_F_sq hH p hpF
  · rw [pow_two]
    calc (f * s.t) * (f * s.t) = (f * f) * (s.t * s.t) := y54_ft_mul hH hf hf
      _ = 1 := by simp [← pow_two, y54_F_sq hH f hf, y54_t_sq s]

private theorem y5_g_comm_P {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hact : ActsAs L g s.fr'.σ) (hgT : g ∈ s.T) :
    ∀ p ∈ f4P s, g * p = p * g := by
  intro p hp
  obtain hpF | ⟨f, hf, rfl⟩ := y54_mem_P s hp
  · have h := y5_g_cent_F hH hg2 hact p hpF
    calc g * p = (g * p * g⁻¹) * g := by group
      _ = p * g := by rw [h]
  · have hgf : g * f = f * g := by
      have h := y5_g_cent_F hH hg2 hact f hf
      calc g * f = (g * f * g⁻¹) * g := by group
        _ = f * g := by rw [h]
    have hgt : g * s.t = s.t * g := s3_comm_t_of_mem_T s hgT
    calc g * (f * s.t) = (g * f) * s.t := by group
      _ = (f * g) * s.t := by rw [hgf]
      _ = f * (g * s.t) := by group
      _ = f * (s.t * g) := by rw [hgt]
      _ = (f * s.t) * g := by group

private theorem y5_gp_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hgp : ∀ p ∈ f4P s, g * p = p * g) {p : G} (hp : p ∈ f4P s) :
    (g * p) * (g * p) = 1 := by
  calc (g * p) * (g * p) = g * ((p * g) * p) := by group
    _ = g * ((g * p) * p) := by rw [(hgp p hp).symm]
    _ = (g * g) * (p * p) := by group
    _ = 1 := by
        rw [y54_gg_eq_one hg2, ← pow_two, y54_P_sq hH p hp, mul_one]

private theorem y54_d_comm_P (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ p ∈ f4P c.s, ⁅c.d, p⁆ ∈ c.s.fr.F := by
  intro p hp
  obtain hpF | ⟨f, hf, rfl⟩ := y54_mem_P c.s hp
  · have h := y54_d_cent_F c p hpF
    rw [commutatorElement_def, h]
    simp
  · have hdf : c.d * f * c.d⁻¹ = f := y54_d_cent_F c f hf
    have hdt : c.d * c.s.t * c.d⁻¹ = c.s.fr.z * c.s.t := y5_dtd hH
    have hfz : f * c.s.fr.z = c.s.fr.z * f :=
      y54_F_comm hH f hf c.s.fr.z (y54_z_mem_F c.s)
    have hcalc : c.d * (f * c.s.t) * c.d⁻¹ * (f * c.s.t)⁻¹ = c.s.fr.z := by
      calc c.d * (f * c.s.t) * c.d⁻¹ * (f * c.s.t)⁻¹
          = (c.d * f * c.d⁻¹) * (c.d * c.s.t * c.d⁻¹) * c.s.t⁻¹ * f⁻¹ := by group
        _ = f * (c.s.fr.z * c.s.t) * c.s.t⁻¹ * f⁻¹ := by rw [hdf, hdt]
        _ = f * c.s.fr.z * f⁻¹ := by group
        _ = c.s.fr.z := by rw [hfz]; group
    rw [commutatorElement_def, hcalc]
    exact y54_z_mem_F c.s

theorem y54_X0_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : ∀ x ∈ f4X0 c.s, x ^ 2 = 1 := by
  intro x hx
  by_cases hRT : c.s.R = c.s.T
  · rw [y54_X0_eq_P hH hRT] at hx
    exact y54_P_sq hH x hx
  · obtain ⟨hgT, -, hact, hg2, -⟩ := c.g_spec hRT
    have hgp : ∀ p ∈ f4P c.s, c.g * p = p * c.g := y5_g_comm_P hH hg2 hact hgT
    rcases y54_X0_cases_g c hH hRT x hx with hxP | hxgx
    · exact y54_P_sq hH x hxP
    · have hxeq : x = c.g * (c.g * x) := by
        rw [← mul_assoc, y54_gg_eq_one hg2, one_mul]
      rw [hxeq, pow_two]
      exact y5_gp_sq hH hg2 hgp hxgx

theorem y54_d_comm_X0 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ x ∈ f4X0 c.s, ⁅c.d, x⁆ ∈ c.s.fr.F := by
  intro x hx
  by_cases hRT : c.s.R = c.s.T
  · rw [y54_X0_eq_P hH hRT] at hx
    exact y54_d_comm_P c hH x hx
  · obtain ⟨hgT, -, hact, hg2, hgd⟩ := c.g_spec hRT
    rcases y54_X0_cases_g c hH hRT x hx with hxP | hxgx
    · exact y54_d_comm_P c hH x hxP
    · have hxeq : x = c.g * (c.g * x) := by
        rw [← mul_assoc, y54_gg_eq_one hg2, one_mul]
      have hdg : c.d * c.g = c.g * c.d := by
        have h : c.g * c.d = c.d * c.g := by
          calc c.g * c.d = (c.g * c.d * c.g⁻¹) * c.g := by group
            _ = c.d * c.g := by rw [hgd]
        exact h.symm
      have hmem : ⁅c.d, c.g * x⁆ ∈ c.s.fr.F := y54_d_comm_P c hH (c.g * x) hxgx
      have hcalc : c.d * (c.g * (c.g * x)) * c.d⁻¹ * (c.g * (c.g * x))⁻¹
          = c.g * ⁅c.d, c.g * x⁆ * c.g⁻¹ := by
        calc c.d * (c.g * (c.g * x)) * c.d⁻¹ * (c.g * (c.g * x))⁻¹
            = (c.d * c.g) * ((c.g * x) * c.d⁻¹ * (c.g * x)⁻¹ * c.g⁻¹) := by group
          _ = (c.g * c.d) * ((c.g * x) * c.d⁻¹ * (c.g * x)⁻¹ * c.g⁻¹) := by rw [hdg]
          _ = c.g * (c.d * (c.g * x) * c.d⁻¹ * (c.g * x)⁻¹) * c.g⁻¹ := by group
          _ = c.g * ⁅c.d, c.g * x⁆ * c.g⁻¹ := by rw [commutatorElement_def]
      rw [hxeq, commutatorElement_def, hcalc]
      rw [y5_g_cent_F hH hg2 hact ⁅c.d, c.g * x⁆ hmem]
      exact hmem

end CFSG.OddStandard.HigherRank.YamadaG23
