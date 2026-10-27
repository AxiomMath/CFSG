module

public import CFSG.GH74.GLS.Stage4.T2NegDefs
public import CFSG.GH74.GLS.Stage4.T2FnH
public import CFSG.GH74.GLS.Stage4.T2Omega1

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG

namespace T2Four1

variable {G : Type} [Group G] {C₁ : Subgroup G} {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}
  (h : T2Four1 C₁ z u K₁ K₂ H w₁ w₂)
include h

theorem w₁_z : w₁ * z = z * w₁ := h.C_comm w₁ (h.K_le_C (Subgroup.mem_sup_left h.w₁_mem))

theorem w₂_z : w₂ * z = z * w₂ := h.C_comm w₂ (h.K_le_C (Subgroup.mem_sup_right h.w₂_mem))

theorem w₁w₂_comm : w₁ * w₂ = w₂ * w₁ := h.K_comm w₁ h.w₁_mem w₂ h.w₂_mem

theorem u_mem_C : u ∈ C₁ := h.H_le_C h.u_mem_H

theorem z_mem_K₁ : z ∈ K₁ := h.w₁_sq ▸ K₁.mul_mem h.w₁_mem h.w₁_mem

theorem z_mem_K₂ : z ∈ K₂ := h.w₂_sq ▸ K₂.mul_mem h.w₂_mem h.w₂_mem

theorem w₀_sq : (w₁ * w₂) * (w₁ * w₂) = 1 := by
  calc (w₁ * w₂) * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
    _ = w₁ * (w₁ * w₂) * w₂ := by rw [← h.w₁w₂_comm]
    _ = (w₁ * w₁) * (w₂ * w₂) := by group
    _ = 1 := by rw [h.w₁_sq, h.w₂_sq, h.zz]

theorem w₁_z' : w₁ * z * w₁⁻¹ = z := by
  calc w₁ * z * w₁⁻¹ = z * w₁ * w₁⁻¹ := by rw [h.w₁_z]
    _ = z := by group

theorem w₀_u : (w₁ * w₂) * u = u * (w₁ * w₂) := by
  have h1 : (w₁ * w₂) * u * (w₁ * w₂)⁻¹ = u := by
    calc (w₁ * w₂) * u * (w₁ * w₂)⁻¹ = w₁ * (w₂ * u * w₂⁻¹) * w₁⁻¹ := by group
      _ = w₁ * (u * z) * w₁⁻¹ := by rw [h.w₂_u]
      _ = (w₁ * u * w₁⁻¹) * (w₁ * z * w₁⁻¹) := by group
      _ = (u * z) * z := by rw [h.w₁_u, h.w₁_z']
      _ = u * (z * z) := by group
      _ = u := by rw [h.zz, mul_one]
  calc (w₁ * w₂) * u = ((w₁ * w₂) * u * (w₁ * w₂)⁻¹) * (w₁ * w₂) := by group
    _ = u * (w₁ * w₂) := by rw [h1]

theorem Y1 : ∀ y ∈ C₁, y * u = u * y → y ∈ H ∨ ∃ x ∈ H, y = x * (w₁ * w₂) := by
  obtain ⟨s₀, hs₀H, hs₀K⟩ := IsConcreteLE.not_le_iff_exists.1 h.H_not_le_K
  exact t2C_Y1 (C₁ := C₁) (H := H) (z := z) (u := u) (w₁ := w₁) (w₂ := w₂) h.K_comm h.K_inter h.zz
    h.C_comm h.K_le_C h.u_mem_C h.C_norm₁ h.C_norm₂ h.uu h.w₁_mem h.w₂_mem h.w₁_u h.w₂_u h.H₁_iff
    h.H₂_iff h.H_comm h.u_mem_H h.H_le_C h.w₀_inv h.C_idx hs₀H hs₀K

theorem omega1 [Finite G] (hr : CFSG.pRank 2 G = 3) :
    ∀ x ∈ H, x * x = 1 → x = 1 ∨ x = z ∨ x = u ∨ x = z * u :=
  t2_omega1_zu hr h.H_comm h.z_mem_H h.u_mem_H h.zz h.uu h.z_ne h.u_ne h.zu_ne h.w₀_sq
    h.w₀_not_mem h.w₀_inv

end T2Four1

end CFSG.GH74.GLS.Stage4.Rest
