module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Frame.exists_rho_hex (d : Std20Frame K K' J S R R' W V z t) :
    ∃ ρ : G, ρ * z * ρ⁻¹ = z * t ∧ ρ * t * ρ⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  refine ⟨t₀ * r, ?_, ?_⟩
  · calc (t₀ * r) * z * (t₀ * r)⁻¹ = t₀ * (r * z * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * z * t₀⁻¹ := by rw [hh.hrz]
      _ = z * t := hh.htz
  · calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
      _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
      _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
      _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
