module

public import Mathlib.GroupTheory.Perm.Centralizer
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Equiv Equiv.Perm Subgroup

theorem perm_involution_cycleType {n : ℕ} (σ : Perm (Fin n)) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ σ.cycleType = Multiset.replicate k 2 := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ) hσ1
  have h2 : ∀ m ∈ σ.cycleType, m = 2 := by
    intro m hm
    have h1 : m ∣ 2 := hord ▸ Equiv.Perm.dvd_of_mem_cycleType hm
    have h3 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
    exact (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h1) h3)
  refine ⟨Multiset.card σ.cycleType, ?_, Multiset.eq_replicate.2 ⟨rfl, h2⟩⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Multiset.card_eq_zero, Equiv.Perm.cycleType_eq_zero] at h0
  exact hσ1 h0

theorem perm_involution_data {n : ℕ} (σ : Perm (Fin n)) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ n ∧ Perm.sign σ = (-1) ^ k ∧
      Nat.card (centralizer ({σ} : Set (Perm (Fin n)))) =
        (n - 2 * k).factorial * 2 ^ k * k.factorial := by
  obtain ⟨k, hk, hct⟩ := perm_involution_cycleType σ hσ hσ1
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · have := Equiv.Perm.sum_cycleType σ
    rw [hct, Multiset.sum_replicate, smul_eq_mul] at this
    have h2 : σ.support.card ≤ n := by
      calc σ.support.card ≤ Finset.univ.card := Finset.card_le_univ _
        _ = n := by simp
    omega
  · rw [Equiv.Perm.sign_of_cycleType, hct]
    simp [Multiset.sum_replicate, pow_add, pow_mul]
  · rw [Equiv.Perm.nat_card_centralizer, hct]
    have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
    rw [hcard, Multiset.sum_replicate, Multiset.prod_replicate, smul_eq_mul, mul_comm k 2]
    have htf : (Multiset.replicate k 2).toFinset = {2} := by
      rw [Multiset.toFinset_replicate]
      simp [Nat.one_le_iff_ne_zero.1 hk]
    rw [htf, Finset.prod_singleton, Multiset.count_replicate_self]

theorem isSolvable_of_card_dvd_two_pow_mul_three_pow {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
  have : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hyz])

end CFSG.GH74.GLS.IVK.GHInv
