module

public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaABaseSq

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem exists_mem_center_sq_eq_of_exponent_two_quotient
    {T : Type*} [Group T] [Finite T] (hcard : Nat.card T = 16)
    {z : T} (hz : z ∈ center T) (hz2 : z * z = 1)
    (hsq : ∀ g : T, g * g = 1 ∨ g * g = z)
    (hno : ∀ w ∈ center T, w * w = 1 → w = 1 ∨ w = z)
    {s : T} (hs : s * s = 1) (hsz : s ∉ center T)
    (hab : ∀ a ∈ centralizer ({s} : Set T), ∀ b ∈ centralizer ({s} : Set T), a * b = b * a)
    (h8 : Nat.card (centralizer ({s} : Set T)) = 8) :
    ∃ v ∈ center T, v * v = z := by
  let C : Subgroup T := centralizer ({s} : Set T)
  have hC8 : Nat.card C = 8 := h8
  have hC8' : (C : Set T).ncard = 8 := h8
  have hsC : s ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hCindex : C.index = 2 := by
    have h := Subgroup.card_mul_index (H := C)
    rw [hcard, hC8] at h
    omega
  have hx_exists : ∃ x : T, x * s ≠ s * x := by
    by_contra h
    push Not at h
    exact hsz ((Subgroup.mem_center_iff).mpr h)
  obtain ⟨x, hxne⟩ := hx_exists
  have hxC : x ∉ C := by
    intro hx
    exact hxne ((Subgroup.mem_centralizer_iff.mp hx s (Set.mem_singleton s)).symm)
  have hxconj : x * s * x⁻¹ = z * s := by
    rcases conj_cases_of_sq_cases hz hz2 hsq x s with h | h
    · exfalso
      apply hxne
      have := congrArg (· * x) h
      simpa [mul_assoc] using this
    · exact h
  have hxs : x * s = z * s * x := by
    have := congrArg (· * x) hxconj
    simpa [mul_assoc] using this
  have hS4 : ({1, s, z, z * s} : Set T).ncard ≤ 4 := by
    have h1 := Set.ncard_insert_le (1 : T) ({s, z, z * s} : Set T)
    have h2 := Set.ncard_insert_le (s : T) ({z, z * s} : Set T)
    have h3 := Set.ncard_insert_le (z : T) ({z * s} : Set T)
    have h4 : ({z * s} : Set T).ncard ≤ 1 := by simp
    omega
  obtain ⟨c, hcC, hcnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := ({1, s, z, z * s} : Set T)) (t := (C : Set T)) (by rw [hC8']; omega)
  have hc1 : c ≠ 1 := fun h => hcnot (by simp [h])
  have hcs : c ≠ s := fun h => hcnot (by simp [h])
  have hcz : c ≠ z := fun h => hcnot (by simp [h])
  have hczs : c ≠ z * s := fun h => hcnot (by simp [h])
  rcases conj_cases_of_sq_cases hz hz2 hsq x c with hxc | hxc
  · have hxc' : x * c = c * x := by
      have := congrArg (· * x) hxc
      simpa [mul_assoc] using this
    have hcenter : c ∈ center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      by_cases hg : g ∈ C
      · exact (hab c hcC g hg).symm
      · have hxC_inv : x⁻¹ ∉ C := fun h => hxC (by simpa using C.inv_mem h)
        have hxg : x⁻¹ * g ∈ C := by
          rw [Subgroup.mul_mem_iff_of_index_two hCindex]
          exact ⟨fun h => absurd h hxC_inv, fun h => absurd h hg⟩
        have hcc' : c * (x⁻¹ * g) = (x⁻¹ * g) * c := hab c hcC (x⁻¹ * g) hxg
        have hg : g = x * (x⁻¹ * g) := (mul_inv_cancel_left x g).symm
        calc g * c = (x * (x⁻¹ * g)) * c := by conv_lhs => rw [hg]
          _ = x * ((x⁻¹ * g) * c) := by group
          _ = x * (c * (x⁻¹ * g)) := by rw [← hcc']
          _ = (x * c) * (x⁻¹ * g) := by group
          _ = (c * x) * (x⁻¹ * g) := by rw [hxc']
          _ = c * (x * (x⁻¹ * g)) := by group
          _ = c * g := by rw [mul_inv_cancel_left x g]
    rcases hsq c with h1 | h1
    · exfalso
      rcases hno c hcenter h1 with h | h
      · exact hc1 h
      · exact hcz h
    · exact ⟨c, hcenter, h1⟩
  · have hxc' : x * c = z * c * x := by
      have := congrArg (· * x) hxc
      simpa [mul_assoc] using this
    have hwC : c * s ∈ C := C.mul_mem hcC hsC
    have hzcs : z * c = c * z := (Subgroup.mem_center_iff.mp hz c).symm
    have hxw : (c * s) * x = x * (c * s) := by
      have key : x * (c * s) * x⁻¹ = c * s := by
        calc x * (c * s) * x⁻¹ = (x * c * x⁻¹) * (x * s * x⁻¹) := by group
          _ = (z * c) * (z * s) := by rw [hxc, hxconj]
          _ = (z * c) * (s * z) := by rw [(Subgroup.mem_center_iff.mp hz s).symm]
          _ = c * s := by
            have hzs : z * s = s * z := (Subgroup.mem_center_iff.mp hz s).symm
            have hzcs2 : (c * s) * z = z * (c * s) :=
              Subgroup.mem_center_iff.mp hz (c * s)
            calc (z * c) * (s * z) = z * (c * (s * z)) := by group
              _ = z * (c * (z * s)) := by rw [hzs]
              _ = z * (z * (c * s)) := by
                    rw [show c * (z * s) = z * (c * s) by
                      rw [hzs, ← hzcs2]; group]
              _ = (z * z) * (c * s) := by group
              _ = c * s := by rw [hz2, one_mul]
      have := congrArg (· * x) key
      have hxw' : x * (c * s) = (c * s) * x := by simpa [mul_assoc] using this
      exact hxw'.symm
    have hcenter : c * s ∈ center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      by_cases hg : g ∈ C
      · exact (hab (c * s) hwC g hg).symm
      · have hxC_inv : x⁻¹ ∉ C := fun h => hxC (by simpa using C.inv_mem h)
        have hxg : x⁻¹ * g ∈ C := by
          rw [Subgroup.mul_mem_iff_of_index_two hCindex]
          exact ⟨fun h => absurd h hxC_inv, fun h => absurd h hg⟩
        have hww' : (c * s) * (x⁻¹ * g) = (x⁻¹ * g) * (c * s) :=
          hab (c * s) hwC (x⁻¹ * g) hxg
        have hg : g = x * (x⁻¹ * g) := (mul_inv_cancel_left x g).symm
        calc g * (c * s) = (x * (x⁻¹ * g)) * (c * s) := by conv_lhs => rw [hg]
          _ = x * ((x⁻¹ * g) * (c * s)) := by group
          _ = x * ((c * s) * (x⁻¹ * g)) := by rw [← hww']
          _ = (x * (c * s)) * (x⁻¹ * g) := by group
          _ = ((c * s) * x) * (x⁻¹ * g) := by rw [← hxw]
          _ = (c * s) * (x * (x⁻¹ * g)) := by group
          _ = (c * s) * g := by rw [mul_inv_cancel_left x g]
    have hws_ne1 : c * s ≠ 1 := by
      intro h
      apply hcs
      have := congrArg (· * s) h
      simpa [mul_assoc, hs] using this
    have hws_nez : c * s ≠ z := by
      intro h
      apply hczs
      have := congrArg (· * s) h
      simpa [mul_assoc, hs] using this
    rcases hsq (c * s) with h1 | h1
    · exfalso
      rcases hno (c * s) hcenter h1 with h | h
      · exact hws_ne1 h
      · exact hws_nez h
    · exact ⟨c * s, hcenter, h1⟩

end CFSG.GroupTheory.SmallFixedTwoGroup
