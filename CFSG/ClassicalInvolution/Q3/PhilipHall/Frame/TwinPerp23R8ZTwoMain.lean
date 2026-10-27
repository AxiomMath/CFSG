module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwo
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoP
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoKF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoY

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE

section Main


variable {n : ℕ}

theorem p23E8ZTwo_proved (hT : Thm4RTwinBelow 3 n) (hTwo : P23Two n)
    (hα : P23Alpha n) : P23E8ZTwo n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZ hAE
  obtain ⟨c', hc'C, hyc, hne, hfield⟩ := exists_y hT hcit hP hTwo hα hc hno hZ hAE
  obtain ⟨D⟩ := exists_cover hc hAE
  set y := c' * e * c'⁻¹ with hydef
  have hyC : y ∈ Subgroup.centralizer ({e} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr hyc
  have hy2 : y * y = 1 := by
    calc y * y = c' * (e * e) * c'⁻¹ := by rw [hydef]; group
      _ = 1 := by rw [hc.data.he2]; group
  have hct : c' * t * c'⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc'C]
    group
  have hyt : y * t = t * y := by
    calc y * t = c' * e * c'⁻¹ * (c' * t * c'⁻¹) := by rw [hct]
      _ = c' * (e * t) * c'⁻¹ := by group
      _ = c' * (t * e) * c'⁻¹ := by rw [e_comm_t hc]
      _ = (c' * t * c'⁻¹) * (c' * e * c'⁻¹) := by group
      _ = t * y := by rw [hct]
  obtain ⟨β, hβ, w, hw, hz, hcase⟩ := y_cases hc D hyC hyt hfield
  rcases hcase with hodd | hT1 | ⟨c₀, hc₀, hcen⟩
  ·
    obtain ⟨ρ, hρs, hρk⟩ := exists_rho_of_odd hc D hyC hy2 hw hodd
    exact ⟨y, hyt, hyc, hy2, hfield, ρ, hρs, hρk⟩
  ·
    exfalso
    have hφ : ∀ q, D.φ (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ q) = D.φ q := by
      intro q
      rw [hw q, hT1, one_mul, inv_one, mul_one]
    have hid := eq_of_trivial_mod_ker D.perfect
      (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) (fun q => by
        apply D.toAEData.ker_le
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel])
    exact false_of_trivial hc D hyC hy2 hne hid
  ·
    exfalso
    exact false_of_zv hT hc hZ D hc'C hyC hy2 hyt hw hz hc₀ hcen

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo
