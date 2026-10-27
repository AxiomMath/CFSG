module

public import CFSG.CGT.Foote81L6.TStruct.E64

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

private theorem zc_succ_eq' (k : ℕ) : zc (k + 1) = r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) := by
  rw [← rho_pow (by omega : 1 ≤ k + 1), r_one_pow, Nat.add_sub_cancel]

theorem mul_self_eq_one_or_zc {a : ℕ} (ha : 1 ≤ a) {d : DihedralGroup (2 ^ a)}
    (h : d * d * (d * d) = 1) : d * d = 1 ∨ d * d = zc a := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rcases d with i | i
  · rw [r_mul_r, r_mul_r, ← r_zero] at h
    rcases eq_zero_or_half (r.inj h) with h0 | hh
    · left
      rw [r_mul_r, h0, r_zero]
    · right
      rw [r_mul_r, hh, zc_succ_eq']
  · left
    rw [sr_mul_sr, sub_self, r_zero]

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem mul_self_mem_T₁_of_mem_T₀ {x : G} (hx : x ∈ D.T₀) : x * x ∈ D.T₁ := by
  rcases D.mem_T₁_or_mul_s_mem_T₁ hx with h | h
  · exact mul_mem h h
  · have hsT : D.s⁻¹ ∈ T := inv_mem (D.B_le_T D.s_mem_B)
    have e : x * x = (x * D.s) * (D.s⁻¹ * (x * D.s) * D.s⁻¹⁻¹) * (D.s * D.s)⁻¹ := by group
    rw [e, D.s_mul_s, inv_one, mul_one]
    exact mul_mem h (D.conj_mem_T₁ hsT h)

theorem mul_self_mem_T₁ {x : G} (hx : x ∈ T) : x * x ∈ D.T₁ := by
  rcases D.mem_T_iff.1 hx with h0 | h0
  · exact D.mul_self_mem_T₁_of_mem_T₀ h0
  · set w := x * D.t with hw
    have hx' : x = w * D.t := by rw [hw, mul_assoc, D.t_mul_t, mul_one]
    have e : x * x = (w * (D.t * w * D.t⁻¹ * w⁻¹) * w⁻¹) * (w * w) := by
      rw [hx', D.t_inv]
      group
    rw [e]
    exact mul_mem (D.conj_mem_T₁ (D.T₀_le_T h0) (D.conj_t_mem_T₁ h0))
      (D.mul_self_mem_T₁_of_mem_T₀ h0)

theorem B₀_iso_apply_b₀ (e : ↥D.B₀ ≃* DihedralGroup (2 ^ (n - 1))) :
    e ⟨D.b₀, D.b₀_mem⟩ = zc (n - 1) := by
  rcases eq_one_or_zc_of_comm (by have := D.three_le_n; omega : 2 ≤ n - 1)
      (c := e ⟨D.b₀, D.b₀_mem⟩) (fun g => by
        obtain ⟨y, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext (D.b₀_comm y y.2))) with h | h
  · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.b₀_ne_one
  · exact h

theorem B₁_iso_apply_b₁ (e : ↥D.B₁ ≃* DihedralGroup (2 ^ (n - 1))) :
    e ⟨D.b₁, D.b₁_mem⟩ = zc (n - 1) := by
  rcases eq_one_or_zc_of_comm (by have := D.three_le_n; omega : 2 ≤ n - 1)
      (c := e ⟨D.b₁, D.b₁_mem⟩) (fun g => by
        obtain ⟨y, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext (D.b₁_comm y y.2))) with h | h
  · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.b₁_ne_one
  · exact h

theorem mul_self_eq_one_or_a {x : G} (hx : x ∈ D.A) (h : x * x * (x * x) = 1) :
    x * x = 1 ∨ x * x = D.a := by
  obtain ⟨e⟩ := D.At_iso
  have hd : e ⟨x, mem_sup_left hx⟩ * e ⟨x, mem_sup_left hx⟩ *
      (e ⟨x, mem_sup_left hx⟩ * e ⟨x, mem_sup_left hx⟩) = 1 := by
    rw [← map_mul, ← map_mul, ← e.map_one]
    exact congrArg e (Subtype.ext h)
  rcases mul_self_eq_one_or_zc D.one_le_m hd with h1 | h1
  · left
    rw [← map_mul, ← e.map_one] at h1
    exact congrArg Subtype.val (e.injective h1)
  · right
    rw [← map_mul, ← D.At_iso_apply_a e] at h1
    exact congrArg Subtype.val (e.injective h1)

theorem mul_self_eq_one_or_b₀ {x : G} (hx : x ∈ D.B₀) (h : x * x * (x * x) = 1) :
    x * x = 1 ∨ x * x = D.b₀ := by
  obtain ⟨e⟩ := D.B₀_iso
  have hd : e ⟨x, hx⟩ * e ⟨x, hx⟩ * (e ⟨x, hx⟩ * e ⟨x, hx⟩) = 1 := by
    rw [← map_mul, ← map_mul, ← e.map_one]
    exact congrArg e (Subtype.ext h)
  rcases mul_self_eq_one_or_zc (by have := D.three_le_n; omega : 1 ≤ n - 1) hd with h1 | h1
  · left
    rw [← map_mul, ← e.map_one] at h1
    exact congrArg Subtype.val (e.injective h1)
  · right
    rw [← map_mul, ← D.B₀_iso_apply_b₀ e] at h1
    exact congrArg Subtype.val (e.injective h1)

theorem mul_self_eq_one_or_b₁ {x : G} (hx : x ∈ D.B₁) (h : x * x * (x * x) = 1) :
    x * x = 1 ∨ x * x = D.b₁ := by
  obtain ⟨e⟩ := D.B₁_iso
  have hd : e ⟨x, hx⟩ * e ⟨x, hx⟩ * (e ⟨x, hx⟩ * e ⟨x, hx⟩) = 1 := by
    rw [← map_mul, ← map_mul, ← e.map_one]
    exact congrArg e (Subtype.ext h)
  rcases mul_self_eq_one_or_zc (by have := D.three_le_n; omega : 1 ≤ n - 1) hd with h1 | h1
  · left
    rw [← map_mul, ← e.map_one] at h1
    exact congrArg Subtype.val (e.injective h1)
  · right
    rw [← map_mul, ← D.B₁_iso_apply_b₁ e] at h1
    exact congrArg Subtype.val (e.injective h1)

theorem mul_self_mem_Zab {v : G} (hv : v ∈ D.T₁) (h4 : v * v * (v * v) = 1) :
    v * v ∈ D.Zab := by
  obtain ⟨x, hx, w, hw, rfl⟩ := D.mem_T₁_iff.1 hv
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  have hsq : ∀ {y y₀ y₁ : G}, y ∈ D.A → y₀ ∈ D.B₀ → y₁ ∈ D.B₁ →
      y * (y₀ * y₁) * (y * (y₀ * y₁)) = (y * y) * ((y₀ * y₀) * (y₁ * y₁)) := by
    intro y y₀ y₁ hy hy₀ hy₁
    have hc : y * (y₀ * y₁) = (y₀ * y₁) * y :=
      D.A_comm_B₀B₁ y hy _ (mul_mem (mem_sup_left hy₀) (mem_sup_right hy₁))
    have hc' : y₀ * y₁ = y₁ * y₀ := D.B₀_comm_B₁ y₀ hy₀ y₁ hy₁
    calc y * (y₀ * y₁) * (y * (y₀ * y₁)) = y * ((y₀ * y₁) * y) * (y₀ * y₁) := by group
      _ = y * (y * (y₀ * y₁)) * (y₀ * y₁) := by rw [← hc]
      _ = y * y * ((y₀ * y₁) * (y₀ * y₁)) := by group
      _ = y * y * ((y₀ * y₀) * (y₁ * y₁)) := by
          rw [show y₀ * y₁ * (y₀ * y₁) = y₀ * (y₁ * y₀) * y₁ by group, ← hc']; group
  rw [hsq hx hw₀ hw₁] at h4 ⊢
  rw [hsq (mul_mem hx hx) (mul_mem hw₀ hw₀) (mul_mem hw₁ hw₁)] at h4
  obtain ⟨hx4, hw4⟩ := D.mul_eq_one_T₀ (mul_mem (mul_mem hx hx) (mul_mem hx hx))
    (D.B₀B₁_le_B (mul_mem (mem_sup_left (mul_mem (mul_mem hw₀ hw₀) (mul_mem hw₀ hw₀)))
      (mem_sup_right (mul_mem (mul_mem hw₁ hw₁) (mul_mem hw₁ hw₁))))) h4
  obtain ⟨hw04, hw14⟩ := D.mul_eq_one_B₀B₁ (mul_mem (mul_mem hw₀ hw₀) (mul_mem hw₀ hw₀))
    (mul_mem (mul_mem hw₁ hw₁) (mul_mem hw₁ hw₁)) hw4
  have ha : D.a ∈ D.Zab := subset_closure (Set.mem_insert _ _)
  have hb₀ : D.b₀ ∈ D.Zab := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb₁ : D.b₁ ∈ D.Zab :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hxZ : x * x ∈ D.Zab := by
    rcases D.mul_self_eq_one_or_a hx hx4 with h | h <;> rw [h]
    · exact one_mem _
    · exact ha
  have hw₀Z : w₀ * w₀ ∈ D.Zab := by
    rcases D.mul_self_eq_one_or_b₀ hw₀ hw04 with h | h <;> rw [h]
    · exact one_mem _
    · exact hb₀
  have hw₁Z : w₁ * w₁ ∈ D.Zab := by
    rcases D.mul_self_eq_one_or_b₁ hw₁ hw14 with h | h <;> rw [h]
    · exact one_mem _
    · exact hb₁
  exact mul_mem hxZ (mul_mem hw₀Z hw₁Z)

end FooteCore

end CFSG.CGT.Foote81L6
