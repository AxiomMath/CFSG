
module

public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public import Certificates.Certificate16963
public import Certificates.Certificate16964

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

theorem stepA {a : V12}
    {D : Submodule (ZMod 2) V12} {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp a D L) :
    ∃ h ∈ gammaU, h a = vecOf a0 ∧ D.map (h : V12 →ₗ[ZMod 2] V12) = spanOf d0 ∧
      ∃ c < 32, ∀ l : V12 ≃ₗ[ZMod 2] V12,
        l ∈ L.map (MulAut.conj h).toMonoidHom ↔ ∃ r ∈ compOf c, ∀ x, l x = linOfRows r x := by
  have h1 := Certificates.certificate16963
  have h2 := Certificates.certificate16964
  obtain ⟨g₁, hg₁, hg₁a⟩ : ∃ g₁ ∈ gammaU, g₁ a = vecOf a0 := by
    obtain ⟨g, hg, hga⟩ := h1.exists_gammaU a H.ne_zero H.q_eq
    exact ⟨g⁻¹, inv_mem hg, by rw [← hga, inv_apply_apply]⟩
  have H₁ := H.conj hg₁
  rw [hg₁a] at H₁
  obtain ⟨rep, hrep, g₂, hg₂, hg₂a, hD₂⟩ := exists_rep h1 H₁
  have H₂ := H₁.conj hg₂
  rw [hg₂a, hD₂] at H₂
  by_cases hrd : rep = d0
  · subst hrd
    obtain ⟨c, hc, hcL⟩ := comp_of_d0 h2 H₂
    refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_, ?_, c, hc, fun l => ?_⟩
    · rw [LinearEquiv.mul_apply, hg₁a, hg₂a]
    · rw [← hD₂]
      ext x
      simp only [Submodule.mem_map, LinearEquiv.coe_coe]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g₁ y, ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, rfl⟩
    · rw [← hcL l, mem_map_conj, mem_map_conj]
      constructor
      · rintro ⟨l₀, hl₀, rfl⟩
        exact ⟨g₁ * l₀ * g₁⁻¹, mem_map_conj.2 ⟨l₀, hl₀, rfl⟩, by group⟩
      · rintro ⟨l₁, hl₁, rfl⟩
        obtain ⟨l₀, hl₀, rfl⟩ := mem_map_conj.1 hl₁
        exact ⟨l₀, hl₀, by group⟩
  · exact (false_of_bad h2 hrep hrd H₂).elim

end CFSG.GF2Type.Smith1979.GammaU.StepA
