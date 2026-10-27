module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type*} [Group G]

structure Setting (L : Subgroup G) (z : G) : Prop where
  z_mul_self : z * z = 1
  z_ne_one : z ≠ 1
  z_not_mem : z ∉ L
  z_comm : ∀ l ∈ L, z * l = l * z
  centralizer_z : ∀ g : G, z * g = g * z → ∃ l ∈ L, g = l ∨ g = l * z
  isSq : ∀ u ∈ L, u * u = 1 → ∃ c ∈ L, c * c = u

namespace Setting

variable {L : Subgroup G} {z : G} (h : Setting L z)
include h

theorem z_ne_sq (g : G) : g * g ≠ z := by
  intro hg
  have hc : z * g = g * z := by
    rw [← hg]; group
  obtain ⟨l, hl, hcases⟩ := h.centralizer_z g hc
  have hsq : g * g ∈ L := by
    rcases hcases with rfl | rfl
    · exact L.mul_mem hl hl
    · have : l * z * (l * z) = l * l * (z * z) := by
        calc l * z * (l * z) = l * (z * l) * z := by simp only [mul_assoc]
          _ = l * (l * z) * z := by rw [h.z_comm l hl]
          _ = l * l * (z * z) := by simp only [mul_assoc]
      rw [this, h.z_mul_self, mul_one]
      exact L.mul_mem hl hl
  exact h.z_not_mem (hg ▸ hsq)

theorem not_isConj_of_sq {u : G} (hu : ∃ c, c * c = u) : ¬ IsConj z u := by
  rintro hcj
  obtain ⟨c, hc⟩ := hu
  obtain ⟨g, hg⟩ := isConj_iff.1 hcj
  refine h.z_ne_sq (g⁻¹ * c * g) ?_
  calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
    _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hc, hg]
    _ = z := by group

theorem not_isConj_z_of_mem {u : G} (hu : u ∈ L) (hu2 : u * u = 1) : ¬ IsConj z u := by
  obtain ⟨c, -, hc⟩ := h.isSq u hu hu2
  exact h.not_isConj_of_sq ⟨c, hc⟩

theorem conj_not_mem_of_mul_self {g : G} (hg : g * z * g⁻¹ ∈ L) : False := by
  have h2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  exact h.not_isConj_z_of_mem hg h2 (isConj_iff.2 ⟨g, rfl⟩)

end Setting

end CFSG.EvenSporadicStandard.J4Std
