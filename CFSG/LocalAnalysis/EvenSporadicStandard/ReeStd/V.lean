module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Setting

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem mem_V_iff {x : G} : x ∈ H.V ↔ x ∈ H.E ∨ x * H.z ∈ H.E := by
  constructor
  · intro hx
    obtain ⟨e, he, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer (A := H.E)
      (B := zpowers H.z) (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun e he =>
        H.z_comm_E he)) hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      have : H.z ^ n = 1 := by
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
      rw [this, mul_one]; exact he
    · right
      have : H.z ^ n = H.z := by
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
      rw [this, mul_assoc, H.z_mul_self, mul_one]; exact he
  · rintro (h | h)
    · exact mem_sup_left h
    · have : x = (x * H.z) * H.z⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers _)))

theorem E_le_V : H.E ≤ H.V := le_sup_left

theorem z_mem_V : H.z ∈ H.V := mem_sup_right (mem_zpowers _)

theorem mem_V_iff' {x : G} : x ∈ H.V ↔ x ∈ H.E ∨ ∃ e ∈ H.E, x = e * H.z := by
  rw [H.mem_V_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨x * H.z, h, ?_⟩
      calc x = x * (H.z * H.z) := by rw [H.z_mul_self, mul_one]
        _ = x * H.z * H.z := by group
  · rintro (h | ⟨e, he, rfl⟩)
    · exact Or.inl h
    · right
      have : e * H.z * H.z = e := by
        calc e * H.z * H.z = e * (H.z * H.z) := by group
          _ = e := by rw [H.z_mul_self, mul_one]
      rw [this]; exact he

end Setting

end CFSG.EvenSporadicStandard.ReeStd
