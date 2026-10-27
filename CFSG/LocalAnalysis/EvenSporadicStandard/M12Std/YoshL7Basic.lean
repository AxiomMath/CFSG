module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshESModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup
open scoped commutatorElement

theorem card_eq_two_pow_of_le {G : Type*} [Group G] [Finite G] (S H : Subgroup G) (hSH : S ≤ H)
    (hS : Nat.card S = 2 ^ (Nat.card G).factorization 2) :
    Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
  have h1 : Nat.card S ∣ Nat.card H := Subgroup.card_dvd_of_le hSH
  have h2 : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card H).factorization 2 ≤ (Nat.card G).factorization 2 :=
    (Nat.factorization_le_iff_dvd hH0 hG0).2 h2 2
  have h4 : (Nat.card G).factorization 2 ≤ (Nat.card H).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hH0]
    rw [hS] at h1
    exact h1
  rw [hS, le_antisymm h4 h3]

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G) (g : G)
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hinv := conj_inv_mem H g h
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := hinv _ hx
  simpa [mul_assoc] using this

theorem conj_mem_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : ∀ x ∈ H, g * x * g⁻¹ ∈ H := fun x hx =>
  (mem_normalizer_iff.1 hg x).1 hx

theorem conj_inv_mem_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : ∀ x ∈ H, g⁻¹ * x * g ∈ H := fun x hx => by
  have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
  simpa using this

theorem mul_self_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {x : G} (h : orderOf x = 2) :
    x * x = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem eq_one_of_odd_orderOf_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  have h2 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h2

theorem exists_conj_of_fusion {G : Type*} [Group G] (L : Subgroup G) (e c d x : G) (hdL : d ∈ L)
    (hde : d * e * d⁻¹ = e * c) (h : ∃ ℓ ∈ L, ℓ * x * ℓ⁻¹ = e ∨ ℓ * x * ℓ⁻¹ = e * c) :
    ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = x := by
  obtain ⟨ℓ, hℓ, h | h⟩ := h
  · refine ⟨ℓ⁻¹, L.inv_mem hℓ, ?_⟩
    rw [← h]
    group
  · refine ⟨ℓ⁻¹ * d, L.mul_mem (L.inv_mem hℓ) hdL, ?_⟩
    have : x = ℓ⁻¹ * (e * c) * ℓ := by rw [← h]; group
    rw [this, ← hde]
    group

end CFSG.EvenSporadicStandard.M12Std.Yosh
