module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27Br

theorem sylow_center_le_commutator {Y : Type*} [Group Y] [Finite Y] (hY : Group.IsPerfect Y)
    (P : Sylow 2 Y) {u : Y} (hu : u ∈ Subgroup.center Y) (huP : u ∈ (P : Subgroup Y)) :
    u ∈ ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ϕ : ↥(P : Subgroup Y) →* Abelianization ↥(P : Subgroup Y) := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * u ^ k * g₀ ∈ (P : Subgroup Y) →
      g₀⁻¹ * u ^ k * g₀ = u ^ k := by
    intro k g₀ _
    have hc : u ^ k ∈ Subgroup.center Y := pow_mem hu k
    rw [Subgroup.mem_center_iff] at hc
    calc g₀⁻¹ * u ^ k * g₀ = g₀⁻¹ * (g₀ * u ^ k) := by rw [hc g₀]; group
      _ = u ^ k := by group
  have h1 : ϕ.transfer u = 1 := by
    have hker : commutator Y ≤ (ϕ.transfer).ker := Abelianization.commutator_subset_ker _
    rw [hY.commutator_eq_top] at hker
    exact (MonoidHom.mem_ker).1 (hker (Subgroup.mem_top u))
  rw [MonoidHom.transfer_eq_pow ϕ u hkey] at h1
  set n := (P : Subgroup Y).index with hn
  have hnodd : ¬ 2 ∣ n := P.not_dvd_index
  have hker : (⟨u ^ n, (P : Subgroup Y).pow_mem huP n⟩ : ↥(P : Subgroup Y)) ∈
      (Abelianization.of (G := ↥(P : Subgroup Y))).ker := (MonoidHom.mem_ker).2 h1
  rw [Abelianization.ker_of] at hker
  have h2 : u ^ n ∈ ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ := by
    have := Subgroup.mem_map_of_mem (P : Subgroup Y).subtype hker
    rw [commutator_def, Subgroup.map_commutator] at this
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨u, huP⟩
  have hk' : orderOf u = 2 ^ k := (Subgroup.orderOf_coe (⟨u, huP⟩ : ↥(P : Subgroup Y))).trans hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have : u = 1 := orderOf_eq_one_iff.1 (by simpa using hk')
    rw [this]
    exact one_mem _
  · have hcop : Nat.Coprime n (orderOf u) := by
      rw [hk']
      exact Nat.Coprime.pow_right k
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnodd))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact pow_mem h2 m

end CFSG.GH74.GLS.Stage2.Local.P27Br
