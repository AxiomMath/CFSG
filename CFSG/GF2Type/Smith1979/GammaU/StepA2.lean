
module

public import CFSG.GF2Type.Smith1979.GammaU.StepA2Base

public import CFSG.GF2Type.Smith1979.GammaU.StepA
public import Certificates.Certificate16965

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

theorem stepA_class
    {a : V12} {D : Submodule (ZMod 2) V12}
    {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp a D L) :
    ∃ h ∈ gammaU, h a = vecOf a0 ∧ D.map (h : V12 →ₗ[ZMod 2] V12) = spanOf d0 ∧
      ∃ i, (i = 0 ∨ i = 1) ∧ ∀ l : V12 ≃ₗ[ZMod 2] V12,
        l ∈ L.map (MulAut.conj h).toMonoidHom ↔ RowsSet (compOf i) l := by
  obtain ⟨h, hh, ha, hD, c, hc, hL⟩ := stepA H
  obtain ⟨i, hi, g, hg, hga, hgD, hgC⟩ := Certificates.certificate16965 c hc
  refine ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, ?_, ?_, i, hi, fun l => ?_⟩
  · rw [LinearEquiv.mul_apply, ha]
    conv_lhs => rw [← hga]
    exact inv_apply_apply g _
  · ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : h x ∈ spanOf d0 := hD ▸ ⟨x, hx, rfl⟩
      rw [hgD, LinearEquiv.coe_coe, LinearEquiv.mul_apply, apply_inv_apply]
      exact hx'
    · intro hy
      rw [hgD] at hy
      rw [← hD] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨x, hx, ?_⟩
      rw [LinearEquiv.coe_coe, LinearEquiv.mul_apply]
      change g⁻¹ (h x) = y
      rw [show h x = g y from hxy, inv_apply_apply]
  · have e1 : l ∈ L.map (MulAut.conj (g⁻¹ * h)).toMonoidHom ↔
        g * l * g⁻¹ ∈ L.map (MulAut.conj h).toMonoidHom := by
      rw [mem_map_conj, mem_map_conj]
      constructor
      · rintro ⟨l₀, hl₀, rfl⟩
        exact ⟨l₀, hl₀, by group⟩
      · rintro ⟨l₀, hl₀, hl⟩
        refine ⟨l₀, hl₀, ?_⟩
        have hl' : l = g⁻¹ * (h * l₀ * h⁻¹) * g := by rw [hl]; group
        rw [hl']
        group
    rw [e1, hL, hgC, show g⁻¹ * (g * l * g⁻¹) * g = l by group, RowsSet]

end CFSG.GF2Type.Smith1979.GammaU.StepA
