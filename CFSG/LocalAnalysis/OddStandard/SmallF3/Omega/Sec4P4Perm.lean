module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4P4PermConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv Equiv.Perm

variable {n : ℕ} {N : Type*} [Group N]

theorem sec4P4_perm_compl_of (hn : 3 ≤ n) (π : N →* Perm (Fin n))
    (hC : π.ker ≤ Subgroup.center N) (h2 : ∀ k ∈ π.ker, k ^ 2 = 1)
    {σ : alternatingGroup (Fin n) →* N} (hσ : ∀ a, π (σ a) = a) {u : N}
    (hu : Perm.sign (π u) = -1) (hu2 : u ^ 2 = 1) :
    (σ.range ⊔ Subgroup.zpowers u) ⊓ π.ker = ⊥ ∧ (σ.range ⊔ Subgroup.zpowers u) ⊔ π.ker = ⊤ := by
  haveI hnormal : σ.range.Normal := sec4P4_perm_range_normal hn π hC h2 hσ
  have hrange : ∀ a : alternatingGroup (Fin n), σ a ∈ σ.range :=
    fun a => MonoidHom.mem_range.2 ⟨a, rfl⟩
  have hzpow : ∀ z ∈ Subgroup.zpowers u, z = 1 ∨ z = u := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hu2' : u ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hu2
    rw [zpow_eq_zpow_emod k hu2']
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left; rw [show k % ((2 : ℕ) : ℤ) = 0 from hk]; simp
    · right; rw [show k % ((2 : ℕ) : ℤ) = 1 from hk]; simp
  constructor
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxM, hxker⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxM
    obtain ⟨a, rfl⟩ := hy
    have hπx : π (σ a * z) = 1 := MonoidHom.mem_ker.mp hxker
    rw [map_mul] at hπx
    rcases hzpow z hz with hz1 | hzu
    · rw [hz1, map_one, mul_one, hσ a] at hπx
      have ha : a = 1 := Subtype.ext (by simpa using hπx)
      rw [ha, map_one, hz1, mul_one]
    · rw [hzu, hσ a] at hπx
      have hpu : π u = ((a : Perm (Fin n)))⁻¹ := eq_inv_of_mul_eq_one_right hπx
      have hmem : π u ∈ alternatingGroup (Fin n) := by
        rw [hpu]
        simpa using Subgroup.inv_mem (alternatingGroup (Fin n)) a.2
      have hsign : Perm.sign (π u) = 1 := Equiv.Perm.mem_alternatingGroup.mp hmem
      exact absurd (hu.symm.trans hsign) (by decide)
  · rw [Subgroup.eq_top_iff']
    intro g
    have key : ∃ y ∈ σ.range ⊔ Subgroup.zpowers u, π y = π g := by
      by_cases hg : π g ∈ alternatingGroup (Fin n)
      · exact ⟨σ ⟨π g, hg⟩, Subgroup.mem_sup_left (hrange _), hσ _⟩
      · have hsign : Perm.sign (π g) = -1 := by
          rcases Int.units_eq_one_or (Perm.sign (π g)) with h | h
          · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hg
          · exact h
        have hmem : π g * (π u)⁻¹ ∈ alternatingGroup (Fin n) := by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsign, hu]
          rw [Int.units_inv_eq_self, Int.units_mul_self]
        refine ⟨σ ⟨π g * (π u)⁻¹, hmem⟩ * u, ?_, ?_⟩
        · exact mul_mem (Subgroup.mem_sup_left (hrange _))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
        · rw [map_mul, hσ, Subgroup.coe_mk, inv_mul_cancel_right]
    obtain ⟨y, hy, hπy⟩ := key
    have hker : y⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπy, inv_mul_cancel]
    rw [← mul_inv_cancel_left y g]
    exact Subgroup.mul_mem_sup hy hker

end CFSG.OddStandard.SmallF3.Omega
