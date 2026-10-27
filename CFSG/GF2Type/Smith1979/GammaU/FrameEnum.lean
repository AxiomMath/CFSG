module

public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

@[expose] def Canon (r : Array ℕ) : Prop := r.size = 12 ∧ ∀ x ∈ r, x < 4096

theorem inv_rows {g gi : Array ℕ} (hg : gammaUN g = true) (hmul : mulR g gi = idR) (y : V12) :
    (toU g hg)⁻¹ y = linOfRows gi y := by
  apply (toU g hg).injective
  rw [apply_inv_apply, toU_apply, ← linOfRows_mulR, hmul, linOfRows_idR]

theorem mem_map_conj_inv {g l : V12 ≃ₗ[ZMod 2] V12} {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} :
    l ∈ L.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * l * g⁻¹ ∈ L := by
  rw [mem_map_conj]
  constructor
  · rintro ⟨l₀, hl₀, rfl⟩
    rw [show g * (g⁻¹ * l₀ * g⁻¹⁻¹) * g⁻¹ = l₀ by group]
    exact hl₀
  · intro h
    exact ⟨g * l * g⁻¹, h, by group⟩

end CFSG.GF2Type.Smith1979.GammaU.StepA
