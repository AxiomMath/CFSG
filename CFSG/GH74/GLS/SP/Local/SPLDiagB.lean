module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

theorem diag_eq_one_or_eq_of_mem_zpowers {X : Type*} [Group X] {g : X} (hg : g * g = 1) {y : X}
    (hy : y ∈ zpowers g) : y = 1 ∨ y = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have h2 : g ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hg
  have hk : g ^ k = g ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h]
    simp
  · right
    rw [hk, h]
    simp

theorem diag_mem_sup_zpowers {X : Type*} [Group X] {N : Subgroup X} {g : X} (hg2 : g * g = 1)
    (hgN : g ∈ normalizer (N : Set X)) {x : X} (hx : x ∈ N ⊔ zpowers g) :
    x ∈ N ∨ x * g ∈ N := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left N (zpowers g) ((zpowers_le).2 hgN)
  rw [← SetLike.mem_coe, hset] at hx
  obtain ⟨n, hn, y, hy, rfl⟩ := hx
  rcases diag_eq_one_or_eq_of_mem_zpowers hg2 hy with rfl | rfl
  · exact Or.inl (by simpa using hn)
  · exact Or.inr (by rw [mul_assoc, hg2, mul_one]; exact hn)

theorem diag_card_sup_zpowers {X : Type*} [Group X] [Finite X] {N : Subgroup X} {g : X}
    (hg2 : g * g = 1) (hgN : g ∈ normalizer (N : Set X)) (hg : g ∉ N) :
    Nat.card ↥(N ⊔ zpowers g) = 2 * Nat.card ↥N := by
  set K := N ⊔ zpowers g with hK
  have hgK : g ∈ K := mem_sup_right (mem_zpowers g)
  have hidx : N.relIndex K = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hgK⟩, fun b => ?_⟩
    have hb := diag_mem_sup_zpowers hg2 hgN b.2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with hb | hb
    · refine Or.inr ⟨hb, fun h => hg ?_⟩
      have := mul_mem (inv_mem hb) h
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨hb, fun h => hg ?_⟩
      have := mul_mem (inv_mem h) hb
      rwa [inv_mul_cancel_left] at this
  have h := Subgroup.relIndex_mul_card (H := N) (K := K)
  rw [inf_eq_left.2 le_sup_left, hidx] at h
  exact h.symm

theorem diag_mem_normalizer_of_central {X : Type*} [Group X] {g : X} (hg : ∀ x : X, x * g = g * x)
    (N : Subgroup X) : g ∈ normalizer (N : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← hg h, mul_inv_cancel_right]

theorem diag_arith {nA c nM nQ k e b : ℕ} (hA : nA ≠ 0) (hM : nM = c * nA ^ 2) (hk : 2 ^ k ∣ nA)
    (hQ : ∀ n, 2 ^ n ∣ nQ → 2 ^ n ≤ 2 * (2 ^ k) ^ 2) (hdvd : 2 ^ e * nM ∣ nQ)
    (hb : 2 ^ b ∣ c) : e + b ≤ 1 := by
  obtain ⟨a, m, hm, hAm⟩ := Nat.exists_eq_two_pow_mul_odd hA
  have hka : k ≤ a := by
    have h1 : 2 ^ k ∣ 2 ^ a * m := hAm ▸ hk
    have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
    have h2 : 2 ^ k ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right Nat.one_lt_two).1 h2
  have h1 : 2 ^ (e + b + 2 * a) ∣ nQ := by
    refine Dvd.dvd.trans ?_ hdvd
    obtain ⟨c', rfl⟩ := hb
    rw [hM, hAm]
    exact ⟨c' * m ^ 2, by ring⟩
  have h2 := hQ _ h1
  have h3 : (2 : ℕ) ^ (e + b + 2 * a) ≤ 2 ^ (2 * a + 1) := by
    calc 2 ^ (e + b + 2 * a) ≤ 2 * (2 ^ k) ^ 2 := h2
      _ ≤ 2 * (2 ^ a) ^ 2 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.pow_le_pow_right Nat.two_pos hka) 2)
      _ = 2 ^ (2 * a + 1) := by ring
  have := (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 h3
  omega

end CFSG.GH74.GLS.SP.Local
