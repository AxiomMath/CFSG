module

public import CFSG.Goldschmidt75.Basic

public section

namespace CFSG.Goldschmidt75

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem mem_commutator_of_mem_center (Q : Sylow p G) {z : G} (hzc : z ∈ center G)
    (hzQ : z ∈ (Q : Subgroup G)) (hzG : z ∈ commutator G) :
    z ∈ ⁅(Q : Subgroup G), (Q : Subgroup G)⁆ := by
  set ϕ : (Q : Subgroup G) →* Abelianization (Q : Subgroup G) := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (Q : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc := mem_center_iff.mp (pow_mem hzc k) g₀
    rw [mul_assoc, ← hc]
    group
  have h1 := MonoidHom.transfer_eq_pow ϕ z hkey
  have h2 : ϕ.transfer z = 1 := Abelianization.commutator_subset_ker _ hzG
  rw [h2] at h1
  have hzi : z ^ (Q : Subgroup G).index ∈ (Q : Subgroup G) := pow_mem hzQ _
  have h3 : (⟨z ^ (Q : Subgroup G).index, hzi⟩ : (Q : Subgroup G)) ∈
      commutator (Q : Subgroup G) := by
    rw [← Abelianization.ker_of]
    exact MonoidHom.mem_ker.mpr h1.symm
  have h4 : z ^ (Q : Subgroup G).index ∈ ⁅(Q : Subgroup G), (Q : Subgroup G)⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨_, h3, rfl⟩
  have hcop : (Q : Subgroup G).index.Coprime (orderOf z) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨z, hzQ⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr Q.not_dvd_index))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem h4 m

end CFSG.Goldschmidt75
