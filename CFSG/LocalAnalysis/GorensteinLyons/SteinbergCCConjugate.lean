module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

variable {G : Type*} [Group G]

theorem mem_conjugate_iff_conj_mem {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem inv_mul_mul_mem_conjugate {H : Subgroup G} {g h : G} (hh : h ∈ H) :
    g⁻¹ * h * g ∈ CFSG.conjugate H g := by
  rw [mem_conjugate_iff_conj_mem, show g * (g⁻¹ * h * g) * g⁻¹ = h by group]
  exact hh

theorem mem_normalizer_iff_conjugate_eq {H : Subgroup G} {g : G} :
    g ∈ normalizer (H : Set G) ↔ CFSG.conjugate H g = H := by
  rw [mem_normalizer_iff]
  constructor
  · intro h
    ext x
    rw [mem_conjugate_iff_conj_mem]
    exact (h x).symm
  · intro h x
    rw [← mem_conjugate_iff_conj_mem, h]

theorem conjugate_conjugate (H : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate H g) h = CFSG.conjugate H (g * h) := by
  ext x
  rw [mem_conjugate_iff_conj_mem, mem_conjugate_iff_conj_mem, mem_conjugate_iff_conj_mem,
    mul_inv_rev]
  group

theorem conjugate_injective (g : G) : Function.Injective fun H : Subgroup G =>
    CFSG.conjugate H g := by
  intro H K h
  ext x
  have h1 := SetLike.ext_iff.mp h (g⁻¹ * x * g)
  simp only [mem_conjugate_iff_conj_mem, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  exact h1

theorem eq_of_orderOf_eq_two_of_isCyclic {X : Type*} [Group X] [Finite X] [IsCyclic X]
    {u v : X} (hu : orderOf u = 2) (hv : orderOf v = 2) : u = v := by
  classical
  have : Fintype X := Fintype.ofFinite X
  by_contra huv
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv
    exact absurd hv (by norm_num)
  have hsub : ({1, u, v} : Finset X) ⊆ Finset.univ.filter (fun x : X => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [← hu]
      exact pow_orderOf_eq_one _
    · rw [← hv]
      exact pow_orderOf_eq_one _
  have hcard : ({1, u, v} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair huv]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hu1.symm, hv1.symm⟩
  have hle := IsCyclic.card_pow_eq_one_le (α := X) (n := 2) (by norm_num)
  have := Finset.card_le_card hsub
  omega

theorem eq_one_or_eq_of_mem_zpowers {z x : G} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hk : z ^ (k % 2) = z ^ k := by simpa [hz] using zpow_mod_orderOf z k
  rw [← hk]
  have h0 : 0 ≤ k % 2 := Int.emod_nonneg _ (by norm_num)
  have h2 : k % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

end CFSG.LocalAnalysis.GorensteinLyons
