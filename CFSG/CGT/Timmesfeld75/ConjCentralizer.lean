module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

theorem centralizer_conjSubgroup_eq (g : G) (S : Subgroup G) :
    Subgroup.centralizer (conjSubgroup g S : Set G) =
      conjSubgroup g (Subgroup.centralizer (S : Set G)) := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' : g * y * g⁻¹ ∈ conjSubgroup g S := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hy
    have h1 := h (g * y * g⁻¹) hy'
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * x * g) * y := by group
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ S := mem_conjSubgroup.mp hy
    have h1 := h (g⁻¹ * y * g) hy'
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = x * y := by group

end CFSG.CGT.Timmesfeld75
