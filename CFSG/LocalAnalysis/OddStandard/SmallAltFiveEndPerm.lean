module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard

open Equiv Equiv.Perm Subgroup

theorem cycleType_eq_replicate_two_of_mul_self_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (h : σ * σ = 1) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
  refine Multiset.eq_replicate_card.2 fun n hn => ?_
  have h1 := Equiv.Perm.two_le_of_mem_cycleType hn
  have h2 : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
  have h3 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  have := Nat.le_of_dvd (by norm_num) (h2.trans h3)
  omega

theorem exists_card_centralizer_involution {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α)
    (h : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ Fintype.card α ∧ Perm.sign σ = (-1) ^ k ∧
      Nat.card (centralizer ({σ} : Set (Perm α))) =
        (Fintype.card α - 2 * k).factorial * 2 ^ k * k.factorial := by
  have hct := cycleType_eq_replicate_two_of_mul_self_eq_one σ h
  set k := Multiset.card σ.cycleType with hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (Equiv.Perm.cycleType_eq_zero.1 (Multiset.card_eq_zero.1 h0)) h1
    · exact h0
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hct, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hprod : σ.cycleType.prod = 2 ^ k := by
    rw [hct, Multiset.prod_replicate]
  have hsupp : 2 * k ≤ Fintype.card α := by
    rw [← hsum, Equiv.Perm.sum_cycleType]
    exact Finset.card_le_univ _
  refine ⟨k, hk1, hsupp, ?_, ?_⟩
  · rw [Equiv.Perm.sign_of_cycleType, hsum, ← hk, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  · rw [Equiv.Perm.nat_card_centralizer, hsum, hprod]
    have hfin : σ.cycleType.toFinset = {2} := by
      rw [hct]
      ext x
      simp only [Multiset.mem_toFinset, Multiset.mem_replicate, Finset.mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩
        rfl
      · rintro rfl
        exact ⟨by omega, rfl⟩
    rw [hfin, Finset.prod_singleton, hct, Multiset.count_replicate_self]

theorem card_centralizer_dvd_of_injective {G K : Type*} [Group G] [Group K] [Finite K]
    (φ : G →* K) (hφ : Function.Injective φ) (t : G) :
    Nat.card (centralizer ({t} : Set G)) ∣ Nat.card (centralizer ({φ t} : Set K)) := by
  have hle : (centralizer ({t} : Set G)).map φ ≤ centralizer ({φ t} : Set K) := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g * t = t * g := mem_centralizer_singleton_iff.mp hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg']
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective hφ] at h1

theorem exists_even_involution_of_alternating {G : Type*} [Group G] {n : ℕ}
    (e : G ≃* alternatingGroup (Fin n)) {t : G} (ht : orderOf t = 2) :
    ∃ σ : Perm (Fin n), σ * σ = 1 ∧ σ ≠ 1 ∧ Perm.sign σ = 1 ∧
      Nat.card (centralizer ({t} : Set G)) ∣ Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) := by
  have hGfin : Finite G := Finite.of_equiv _ e.symm.toEquiv
  set φ : G →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ := (Subgroup.subtype_injective _).comp e.injective
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  refine ⟨φ t, ?_, ?_, ?_, card_centralizer_dvd_of_injective φ hφinj t⟩
  · rw [← map_mul, htt, map_one]
  · intro h
    exact ht1 (hφinj (by rw [h, map_one]))
  · exact Equiv.Perm.mem_alternatingGroup.1 (e t).2

theorem card_centralizer_dvd_forty_eight_of_alternating_seven {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 7)) {t : G} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set G)) ∣ 48 := by
  obtain ⟨σ, h2, h1, hs, hd⟩ := exists_even_involution_of_alternating e ht
  obtain ⟨k, hk1, hk2, hsign, hcard⟩ := exists_card_centralizer_involution σ h2 h1
  rw [Fintype.card_fin] at hk2 hcard
  rw [hs] at hsign
  have hk : Even k := (neg_one_pow_eq_one_iff_even (by decide)).1 hsign.symm
  have hk2' : k = 2 := by
    obtain ⟨m, rfl⟩ := hk
    omega
  subst hk2'
  refine hd.trans ?_
  rw [hcard]
  norm_num [Nat.factorial]

theorem not_five_dvd_card_centralizer_of_alternating_eight {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 8)) {t : G} (ht : orderOf t = 2) :
    ¬ 5 ∣ Nat.card (centralizer ({t} : Set G)) := by
  obtain ⟨σ, h2, h1, hs, hd⟩ := exists_even_involution_of_alternating e ht
  obtain ⟨k, hk1, hk2, hsign, hcard⟩ := exists_card_centralizer_involution σ h2 h1
  rw [Fintype.card_fin] at hk2 hcard
  rw [hs] at hsign
  have hk : Even k := (neg_one_pow_eq_one_iff_even (by decide)).1 hsign.symm
  intro h5
  have h5' := h5.trans hd
  rw [hcard] at h5'
  obtain ⟨m, rfl⟩ := hk
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl <;> norm_num [Nat.factorial] at h5'

end CFSG.OddStandard
