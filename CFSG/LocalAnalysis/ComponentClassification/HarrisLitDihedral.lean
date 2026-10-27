module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.ComponentClassification.HarrisLit

open Subgroup DihedralGroup

variable {m : ℕ}

theorem zmod_four_ne_zero (hm : 3 ≤ m) : (4 : ZMod (2 ^ m)) ≠ 0 := by
  intro h
  have h4 : ((4 : ℕ) : ZMod (2 ^ m)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h4
  have := Nat.le_of_dvd (by norm_num) h4
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem r_mem_center_of_two_mul (i : ZMod (2 ^ m)) (hi : 2 * i = 0) :
    r i ∈ center (DihedralGroup (2 ^ m)) := by
  rw [mem_center_iff]
  rintro (j | j)
  · rw [r_mul_r, r_mul_r, add_comm]
  · rw [sr_mul_r, r_mul_sr]
    congr 1
    have : i = -i := by
      rw [eq_neg_iff_add_eq_zero, ← two_mul, hi]
    rw [sub_eq_add_neg, ← this]

theorem dihedral_normal_le_center (hm : 3 ≤ m) (N : Subgroup (DihedralGroup (2 ^ m)))
    [N.Normal] (hN : ∀ x ∈ N, x ^ 2 = 1) : N ≤ center (DihedralGroup (2 ^ m)) := by
  rintro (i | j) hx
  · have h2 := hN _ hx
    rw [sq, r_mul_r, ← r_zero] at h2
    exact r_mem_center_of_two_mul i (by rw [two_mul]; exact r.inj h2)
  · exfalso
    have hc : r 1 * sr j * (r 1)⁻¹ ∈ N := Normal.conj_mem inferInstance _ hx _
    rw [inv_r, r_mul_sr, sr_mul_r] at hc
    have hp := N.mul_mem hx hc
    rw [sr_mul_sr] at hp
    have h2 := hN _ hp
    rw [sq, r_mul_r, ← r_zero] at h2
    have h4 := r.inj h2
    apply zmod_four_ne_zero hm
    have : (j - 1 + -1 - j) + (j - 1 + -1 - j) = -4 := by ring
    rw [this, neg_eq_zero] at h4
    exact h4

theorem dihedral_involution_mem_center (hm : 3 ≤ m) (d : DihedralGroup (2 ^ m))
    (hd : d ^ 2 = 1) (h : ∀ g, d⁻¹ * g⁻¹ * d * g ∈ center (DihedralGroup (2 ^ m))) :
    d ∈ center (DihedralGroup (2 ^ m)) := by
  rcases d with i | j
  · rw [sq, r_mul_r, ← r_zero] at hd
    exact r_mem_center_of_two_mul i (by rw [two_mul]; exact r.inj hd)
  · exfalso
    have h1 := h (r 1)
    rw [inv_sr, inv_r, sr_mul_r, sr_mul_sr, r_mul_r] at h1
    have h2 := (mem_center_iff.mp h1) (sr 0)
    rw [sr_mul_r, r_mul_sr, sr.injEq] at h2
    apply zmod_four_ne_zero hm
    have : (0 : ZMod (2 ^ m)) + (j - (j + -1) + 1) - (0 - (j - (j + -1) + 1)) = 4 := by ring
    rw [← this, h2, sub_self]


section Transfer

variable {G : Type*} [Group G]

theorem dihedral_center_eq (e : G ≃* DihedralGroup (2 ^ m)) (hm : 3 ≤ m) :
    center G = zpowers (e.symm (r ((2 ^ m / 2 : ℕ) : ZMod (2 ^ m)))) := by
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hc := DihedralGroup.center_eq_closure_of_even_ne_two (n := 2 ^ m)
    ((Nat.even_pow' (by omega)).mpr even_two) (by omega)
  rw [← Subgroup.map_center_eq e.symm, hc]
  exact MonoidHom.map_zpowers (e.symm : DihedralGroup (2 ^ m) →* G) _

theorem dihedral_normal_le_center' (e : G ≃* DihedralGroup (2 ^ m)) (hm : 3 ≤ m)
    (N : Subgroup G) [hN' : N.Normal]
    (hN : ∀ x ∈ N, x ^ 2 = 1) : N ≤ center G := by
  have hNe : (N.map (e : G →* DihedralGroup (2 ^ m))).Normal := hN'.map _ e.surjective
  have h1 := dihedral_normal_le_center hm (N.map (e : G →* DihedralGroup (2 ^ m)))
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hN x hx, map_one])
  intro x hx
  have h2 : e x ∈ center (DihedralGroup (2 ^ m)) := h1 ⟨x, hx, rfl⟩
  rw [← Subgroup.map_center_eq e] at h2
  obtain ⟨y, hy, hyx⟩ := h2
  rwa [e.injective hyx] at hy

theorem dihedral_involution_mem_center' (e : G ≃* DihedralGroup (2 ^ m)) (hm : 3 ≤ m) (d : G)
    (hd : d ^ 2 = 1)
    (h : ∀ g, d⁻¹ * g⁻¹ * d * g ∈ center G) : d ∈ center G := by
  have h1 := dihedral_involution_mem_center hm (e d) (by rw [← map_pow, hd, map_one])
    (fun g => by
      have h2 : e (d⁻¹ * (e.symm g)⁻¹ * d * e.symm g) ∈ center (DihedralGroup (2 ^ m)) := by
        rw [← Subgroup.map_center_eq e]
        exact ⟨_, h (e.symm g), rfl⟩
      simpa using h2)
  rw [← Subgroup.map_center_eq e] at h1
  obtain ⟨y, hy, hyd⟩ := h1
  rwa [e.injective hyd] at hy

end Transfer

end CFSG.ComponentClassification.HarrisLit
