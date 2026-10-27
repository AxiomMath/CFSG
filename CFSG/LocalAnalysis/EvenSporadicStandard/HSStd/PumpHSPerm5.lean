module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open Subgroup

theorem cycleType_eq_of_pow_three {σ : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {3} := by
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  have hp : (orderOf σ).Prime := by rw [hord]; exact Nat.prime_three
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [hord] at hn
  have hsum : σ.cycleType.sum ≤ 5 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have : n = 0 := by omega
  rw [hn, this]
  rfl

theorem card_centralizer_perm5_three {σ : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    Nat.card (centralizer ({σ} : Set (Equiv.Perm (Fin 5)))) = 6 := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_eq_of_pow_three h3 h1]
  simp

theorem eq_one_of_pow_five_of_comm {σ s : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (hs5 : s ^ 5 = 1) (hc : s * σ = σ * s) : s = 1 := by
  have hmem : s ∈ centralizer ({σ} : Set (Equiv.Perm (Fin 5))) :=
    mem_centralizer_singleton_iff.2 hc
  have h6 : (⟨s, hmem⟩ : centralizer ({σ} : Set (Equiv.Perm (Fin 5)))) ^
      Nat.card (centralizer ({σ} : Set (Equiv.Perm (Fin 5)))) = 1 := pow_card_eq_one'
  rw [card_centralizer_perm5_three h3 h1] at h6
  have h6' : s ^ 6 = 1 := congrArg Subtype.val h6
  calc s = s ^ 6 * (s ^ 5)⁻¹ := by group
    _ = 1 := by rw [h6', hs5]; simp

theorem eq_or_inv_of_pow_three_of_comm {σ s : Equiv.Perm (Fin 5)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (hc : s * σ = σ * s) : s = σ ∨ s = σ⁻¹ := by
  set C : Subgroup (Equiv.Perm (Fin 5)) := centralizer ({σ} : Set (Equiv.Perm (Fin 5))) with hC
  have hσC : σ ∈ C := mem_centralizer_singleton_iff.2 rfl
  have hsC : s ∈ C := mem_centralizer_singleton_iff.2 hc
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  set N : Subgroup C := zpowers (⟨σ, hσC⟩ : C) with hN
  have hNcard : Nat.card N = 3 := by
    rw [hN, Nat.card_zpowers, Subgroup.orderOf_mk σ hσC, hord]
  have hCcard : Nat.card C = 6 := card_centralizer_perm5_three h3 h1
  have hidx : N.index = 2 := by
    have := N.card_mul_index
    rw [hNcard, hCcard] at this
    omega
  have hNn : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have hq : Nat.card (C ⧸ N) = 2 := by rw [← Subgroup.index, hidx]
  have hsq : ∀ q : C ⧸ N, q ^ 2 = 1 := by
    intro q
    have := pow_card_eq_one' (G := C ⧸ N) (x := q)
    rwa [hq] at this
  have hs3' : ((⟨s, hsC⟩ : C) : C) ^ 3 = 1 := Subtype.ext hs3
  have hmk : (QuotientGroup.mk (⟨s, hsC⟩ : C) : C ⧸ N) = 1 := by
    have h3' : (QuotientGroup.mk (⟨s, hsC⟩ : C) : C ⧸ N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hs3', QuotientGroup.mk_one]
    have h2' := hsq (QuotientGroup.mk (⟨s, hsC⟩ : C))
    calc (QuotientGroup.mk (⟨s, hsC⟩ : C) : C ⧸ N)
        = (QuotientGroup.mk (⟨s, hsC⟩ : C) : C ⧸ N) ^ 3 *
            ((QuotientGroup.mk (⟨s, hsC⟩ : C) : C ⧸ N) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2']; simp
  have hsN : (⟨s, hsC⟩ : C) ∈ N := (QuotientGroup.eq_one_iff _).1 hmk
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hsN
  have hk' : s = σ ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  have hmod : σ ^ k = σ ^ (k % 3 : ℤ) := by
    rw [← zpow_mod_orderOf, hord]
    simp
  have hk3 : (k % 3 : ℤ) = 0 ∨ (k % 3 : ℤ) = 1 ∨ (k % 3 : ℤ) = 2 := by omega
  rcases hk3 with h | h | h
  · exact absurd (by rw [hk', hmod, h]; simp) hs1
  · left
    rw [hk', hmod, h]
    simp
  · right
    rw [hk', hmod, h]
    have : σ ^ (2 : ℤ) = σ⁻¹ := by
      have h31 : σ ^ (3 : ℤ) = 1 := by exact_mod_cast h3
      calc σ ^ (2 : ℤ) = σ ^ (3 : ℤ) * σ⁻¹ := by group
        _ = σ⁻¹ := by rw [h31, one_mul]
    exact this

end CFSG.EvenSporadicStandard.HSStd.PumpHS
