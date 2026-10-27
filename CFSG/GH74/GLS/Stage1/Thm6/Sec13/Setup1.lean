module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_zpowers_involution {x g : G} (hx : x * x = 1) : g ∈ zpowers x ↔ g = 1 ∨ g = x := by
  constructor
  · rintro ⟨k, hk⟩
    have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
    have hk' : x ^ k = g := hk
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      have : (k : ℤ) = 2 * (k / 2) := by omega
      rw [← hk', this, zpow_mul]
      simp [h2]
    · right
      have : (k : ℤ) = 2 * (k / 2) + 1 := by omega
      rw [← hk', this, zpow_add, zpow_mul]
      simp [h2]
  · rintro (h | h)
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers _

theorem V_le_EV {x : G} {V : Subgroup G} : V ≤ EV x V := le_sup_left

theorem x_mem_EV {x : G} {V : Subgroup G} : x ∈ EV x V := Subgroup.mem_sup_right (mem_zpowers x)

namespace Out12

variable {x : G} {T V : Subgroup G} (h : Out12 G x T V)
include h

theorem x_comm {v : G} (hv : v ∈ V) : x * v = v * x := by
  have : v ∈ centralizer ({x} : Set G) := h.T_sylow.1 (h.V_le hv)
  exact mem_centralizer_iff.1 this x rfl

theorem V_sq {v : G} (hv : v ∈ V) : v * v = 1 := (h.V_four.1 v hv).1

theorem V_comm {u v : G} (hu : u ∈ V) (hv : v ∈ V) : u * v = v * u := (h.V_four.1 u hu).2 v hv

theorem x_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right h.x_sq

theorem mem_EV {g : G} : g ∈ EV x V ↔ ∃ v ∈ V, g = v ∨ g = v * x := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ v ∈ V, g = v ∨ g = v * x}
        one_mem' := ⟨1, V.one_mem, Or.inl rfl⟩
        mul_mem' := by
          intro a b ha hb
          obtain ⟨u, hu, ha | ha⟩ := ha <;> obtain ⟨w, hw, hb | hb⟩ := hb <;> rw [ha, hb]
          · exact ⟨u * w, V.mul_mem hu hw, Or.inl rfl⟩
          · exact ⟨u * w, V.mul_mem hu hw, Or.inr (by rw [mul_assoc])⟩
          · refine ⟨u * w, V.mul_mem hu hw, Or.inr ?_⟩
            calc u * x * w = u * (x * w) := by group
              _ = u * (w * x) := by rw [h.x_comm hw]
              _ = u * w * x := by group
          · refine ⟨u * w, V.mul_mem hu hw, Or.inl ?_⟩
            calc u * x * (w * x) = u * (x * w) * x := by group
              _ = u * (w * x) * x := by rw [h.x_comm hw]
              _ = u * w * (x * x) := by group
              _ = u * w := by rw [h.x_sq, mul_one]
        inv_mem' := by
          intro a ha
          obtain ⟨u, hu, ha | ha⟩ := ha <;> rw [ha]
          · exact ⟨u⁻¹, V.inv_mem hu, Or.inl rfl⟩
          · refine ⟨u⁻¹, V.inv_mem hu, Or.inr ?_⟩
            calc (u * x)⁻¹ = x⁻¹ * u⁻¹ := by group
              _ = x * u⁻¹ := by rw [h.x_inv]
              _ = u⁻¹ * x := h.x_comm (V.inv_mem hu) }
    have hle : EV x V ≤ S := by
      refine sup_le (fun v hv => ⟨v, hv, Or.inl rfl⟩) ?_
      rw [zpowers_le]
      exact ⟨1, V.one_mem, Or.inr (by simp)⟩
    exact hle hg
  · rintro ⟨v, hv, hg | hg⟩ <;> rw [hg]
    · exact Subgroup.mem_sup_left hv
    · exact (EV x V).mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (mem_zpowers x))

theorem comm_V_Vx {u w : G} (hu : u ∈ V) (hw : w ∈ V) : u * (w * x) = (w * x) * u := by
  calc u * (w * x) = (u * w) * x := by group
    _ = (w * u) * x := by rw [h.V_comm hu hw]
    _ = w * (u * x) := by group
    _ = w * (x * u) := by rw [h.x_comm hu]
    _ = w * x * u := by group

theorem EV_comm {a b : G} (ha : a ∈ EV x V) (hb : b ∈ EV x V) : a * b = b * a := by
  obtain ⟨u, hu, ha | ha⟩ := (h.mem_EV).1 ha <;> obtain ⟨w, hw, hb | hb⟩ := (h.mem_EV).1 hb <;>
    rw [ha, hb]
  · exact h.V_comm hu hw
  · exact h.comm_V_Vx hu hw
  · exact (h.comm_V_Vx hw hu).symm
  · have e1 : u * x * (w * x) = u * w := by
      calc u * x * (w * x) = u * (x * w) * x := by group
        _ = u * (w * x) * x := by rw [h.x_comm hw]
        _ = u * w * (x * x) := by group
        _ = u * w := by rw [h.x_sq, mul_one]
    have e2 : w * x * (u * x) = w * u := by
      calc w * x * (u * x) = w * (x * u) * x := by group
        _ = w * (u * x) * x := by rw [h.x_comm hu]
        _ = w * u * (x * x) := by group
        _ = w * u := by rw [h.x_sq, mul_one]
    rw [e1, e2, h.V_comm hu hw]

theorem EV_sq {a : G} (ha : a ∈ EV x V) : a * a = 1 := by
  obtain ⟨u, hu, ha | ha⟩ := (h.mem_EV).1 ha <;> rw [ha]
  · exact h.V_sq hu
  · calc u * x * (u * x) = u * (x * u) * x := by group
      _ = u * (u * x) * x := by rw [h.x_comm hu]
      _ = u * u * (x * x) := by group
      _ = 1 := by rw [h.x_sq, h.V_sq hu, mul_one]

theorem EV_elemAb : IsElemAb2 (EV x V) := fun _ ha => ⟨h.EV_sq ha, fun _ hb => h.EV_comm ha hb⟩

end Out12

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
