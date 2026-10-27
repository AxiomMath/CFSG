module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup

variable {G : Type*} [Group G]

theorem mem_comm_pair {z x h : G} :
    h ∈ (centralizer {z} ⊓ centralizer {x} : Subgroup G) ↔ h * z = z * h ∧ h * x = x * h := by
  rw [mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]

@[expose] def swapEquiv (z g : G) :
    (centralizer {z} ⊓ centralizer {g * z * g⁻¹} : Subgroup G) ≃*
      (centralizer {z} ⊓ centralizer {g⁻¹ * z * g} : Subgroup G) where
  toFun h := ⟨g⁻¹ * (h : G) * g, mem_comm_pair.2 (by
    obtain ⟨hz, hx⟩ := mem_comm_pair.1 h.2
    refine ⟨?_, ?_⟩
    · calc g⁻¹ * (h : G) * g * z = g⁻¹ * ((h : G) * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * (h : G)) * g := by rw [hx]
        _ = z * (g⁻¹ * (h : G) * g) := by group
    · calc g⁻¹ * (h : G) * g * (g⁻¹ * z * g) = g⁻¹ * ((h : G) * z) * g := by group
        _ = g⁻¹ * (z * (h : G)) * g := by rw [hz]
        _ = (g⁻¹ * z * g) * (g⁻¹ * (h : G) * g) := by group)⟩
  invFun h := ⟨g * (h : G) * g⁻¹, mem_comm_pair.2 (by
    obtain ⟨hz, hx⟩ := mem_comm_pair.1 h.2
    refine ⟨?_, ?_⟩
    · calc g * (h : G) * g⁻¹ * z = g * ((h : G) * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * (h : G)) * g⁻¹ := by rw [hx]
        _ = z * (g * (h : G) * g⁻¹) := by group
    · calc g * (h : G) * g⁻¹ * (g * z * g⁻¹) = g * ((h : G) * z) * g⁻¹ := by group
        _ = g * (z * (h : G)) * g⁻¹ := by rw [hz]
        _ = (g * z * g⁻¹) * (g * (h : G) * g⁻¹) := by group)⟩
  left_inv h := Subtype.ext (by simp only; group)
  right_inv h := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem exists_swap {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ (g * z * g⁻¹) * z = z * (g * z * g⁻¹) ∧
      orderOf (g * z * g⁻¹) = 2 ∧ orderOf (g⁻¹ * z * g) = 2 ∧ g⁻¹ * z * g ≠ z ∧
      (g⁻¹ * z * g) * z = z * (g⁻¹ * z * g) := by
  obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution hnonab hz
  have hx2 : orderOf (g * z * g⁻¹) = 2 := by
    rw [show g * z * g⁻¹ = MulAut.conj g z by simp, MulEquiv.orderOf_eq, hz]
  have hz'2 : orderOf (g⁻¹ * z * g) = 2 := by
    rw [show g⁻¹ * z * g = MulAut.conj g⁻¹ z by simp, MulEquiv.orderOf_eq, hz]
  refine ⟨g, hne, hcomm, hx2, hz'2, fun h => hne ?_, ?_⟩
  · have h1 : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rwa [h] at h1
  · calc (g⁻¹ * z * g) * z = g⁻¹ * (z * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * z) * g := by rw [hcomm]
      _ = z * (g⁻¹ * z * g) := by group

end CFSG.EvenSporadicStandard.TwoSuz
