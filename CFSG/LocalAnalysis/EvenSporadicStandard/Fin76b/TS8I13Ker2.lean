module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Ctx

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c

theorem eq_one_or_t_of_sq {a : G} (ha : a ∈ c.Zs) (h : a * z * (a * z) = 1) :
    a = 1 ∨ a = t := by
  have hαt : z * (α * t) * z⁻¹ = α := by
    calc z * (α * t) * z⁻¹ = (z * α * z⁻¹) * (z * t * z⁻¹) := by group
      _ = α * t * t := by rw [c.h.z_conj_alpha c.hα, c.h.z_conj_t]
      _ = α := by rw [mul_assoc, c.h.t_sq, mul_one]
  have h2 : a * (z * a * z⁻¹) = 1 := by
    have : a * z * (a * z) = a * (z * a * z⁻¹) * (z * z) := by group
    rwa [this, c.h.z_sq, mul_one] at h
  rcases c.mem_Zs.1 ha with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rw [h1, c.h.z_conj_alpha c.hα, ← mul_assoc, c.hα.sq, one_mul] at h2
    exact c.h.t_ne h2
  · exfalso
    rw [h1, hαt] at h2
    have : α * t * α = t := by
      have := c.h.t_comm_S α c.hα.mem
      calc α * t * α = t * α * α := by rw [← this]
        _ = t := by rw [mul_assoc, c.hα.sq, mul_one]
    rw [this] at h2
    exact c.h.t_ne h2

theorem t_mul_z : t * z = α * z * α⁻¹ := by
  have hzα : z * α = α * t * z := by
    have := c.h.z_conj_alpha c.hα
    calc z * α = (z * α * z⁻¹) * z := by group
      _ = α * t * z := by rw [this]
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right c.hα.sq
  symm
  calc α * z * α⁻¹ = α * (z * α) := by rw [hαi]; group
    _ = α * (α * t * z) := by rw [hzα]
    _ = t * z := by rw [← mul_assoc α, ← mul_assoc α, c.hα.sq, one_mul]

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
