module

public import CFSG.GH74.Uniqueness.Bender.Dickson

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Linear

variable {K : Type*} [Group K]

theorem zpowers_involution_cases {w : K} (hw2 : w * w = 1) {g : K} (hg : g ∈ zpowers w) :
    g = 1 ∨ g = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul]
    have : w ^ (2 : ℤ) = 1 := by rw [zpow_two, hw2]
    rw [this, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul]
    have : w ^ (2 : ℤ) = 1 := by rw [zpow_two, hw2]
    rw [this, one_zpow, one_mul]

variable [Finite K]

theorem BenderType.linear_odd_subgroup
    {n : ℕ} (h : BenderType K n 1 1) {A : Subgroup K}
    (hA : Odd (Nat.card A)) (hA1 : A ≠ ⊥) :
    ∃ (T : Subgroup K) (w : K), A ≤ T ∧ IsCyclic T ∧ Odd (Nat.card T) ∧
      (Nat.card T = 2 ^ n - 1 ∨ Nat.card T = 2 ^ n + 1) ∧ w * w = 1 ∧ w ≠ 1 ∧
      (∀ c ∈ T, w * c * w⁻¹ = c⁻¹) ∧ normalizer (A : Set K) = T ⊔ zpowers w ∧
      (∀ y : K, y * y = 1 → y ≠ 1 → y ∈ normalizer (A : Set K) → ∀ c ∈ T, y * c * y⁻¹ = c⁻¹) := by
  classical
  have hn2 : 2 ≤ n := h.two_le.2
  obtain ⟨N, ⟨x, w, hx1, hxodd, hw2, hcyc, hcard, hinv, hNeq, hNR⟩, hAN⟩ := h.lemma_3_7_odd A hA
  set T : Subgroup K := centralizer ({x} : Set K) with hT
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hpos : 0 < 2 ^ n := by positivity
  have hTodd : Odd (Nat.card T) := by
    rcases hcard with h1 | h1
    · rw [h1]
      exact Nat.odd_iff.mpr (by omega)
    · rw [h1]
      exact Nat.odd_iff.mpr (by omega)
  have hxT : x ∈ T := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hTsq : ∀ y ∈ T, y * y = 1 → y = 1 := by
    intro y hyT hy2
    have h1 : orderOf y ∣ Nat.card T := by
      have := _root_.orderOf_dvd_natCard (⟨y, hyT⟩ : T)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy2)
    have h3 : Odd (orderOf y) := Odd.of_dvd_nat hTodd h1
    have h4 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h5 | h5
      · exact h5
      · rw [h5] at h3
        exact absurd h3 (by decide)
    exact orderOf_eq_one_iff.mp h4
  have hw1 : w ≠ 1 := by
    intro hw
    have h1 := hinv x hxT
    rw [hw] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    apply hx1
    apply hTsq x hxT
    calc x * x = x * x⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel x
  have hwN : zpowers w ≤ normalizer (T : Set K) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      rw [hinv g hg]
      exact T.inv_mem hg
    · intro hg
      have h1 := hinv _ hg
      have h2 : w * (w * g * w⁻¹) * w⁻¹ = g := by
        rw [hwi]
        calc w * (w * g * w) * w = (w * w) * g * (w * w) := by group
          _ = g := by rw [hw2]; group
      rw [h2] at h1
      rw [h1]
      exact T.inv_mem hg
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left T (zpowers w) hwN
  have hsplit : ∀ a ∈ T ⊔ zpowers w, a ∈ T ∨ a * a = 1 := by
    intro a ha
    have ha' : a ∈ ((T ⊔ zpowers w : Subgroup K) : Set K) := ha
    rw [hset] at ha'
    obtain ⟨c, hc, g, hg, rfl⟩ := Set.mem_mul.mp ha'
    rcases zpowers_involution_cases hw2 hg with hg1 | hg1
    · left
      rw [hg1, mul_one]
      exact hc
    · right
      rw [hg1]
      have h1 := hinv c hc
      rw [hwi] at h1
      calc c * w * (c * w) = c * (w * c * w) := by group
        _ = 1 := by rw [h1]; group
  have hAT : A ≤ T := by
    intro a ha
    have haN : a ∈ T ⊔ zpowers w := by
      rw [← hNeq]
      exact hAN ha
    rcases hsplit a haN with h1 | h1
    · exact h1
    · have h2 : orderOf a ∣ Nat.card A := by
        have := _root_.orderOf_dvd_natCard (⟨a, ha⟩ : A)
        rwa [Subgroup.orderOf_mk] at this
      have h3 : Odd (orderOf a) := Odd.of_dvd_nat hA h2
      have h4 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
      have h5 : orderOf a = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h6 | h6
        · exact h6
        · rw [h6] at h3
          exact absurd h3 (by decide)
      rw [orderOf_eq_one_iff.mp h5]
      exact T.one_mem
  have hAne : normalizer (A : Set K) = T ⊔ zpowers w := by
    rw [hNR A hAT hA1, hNeq]
  refine ⟨T, w, hAT, hcyc, hTodd, hcard, hw2, hw1, hinv, hAne, ?_⟩
  intro y hy2 hy1 hyA c hc
  have hyN : y ∈ T ⊔ zpowers w := by
    rw [← hAne]
    exact hyA
  have hy' : y ∈ ((T ⊔ zpowers w : Subgroup K) : Set K) := hyN
  rw [hset] at hy'
  obtain ⟨d, hd, g, hg, rfl⟩ := Set.mem_mul.mp hy'
  rcases zpowers_involution_cases hw2 hg with hg1 | hg1
  · exfalso
    rw [hg1, mul_one] at hy2 hy1
    exact hy1 (hTsq d hd hy2)
  · rw [hg1]
    have h1 := hinv c hc
    have hcomm : c * d = d * c := by
      have := (IsMulCommutative.is_comm (M := ↥T)).comm ⟨c, hc⟩ ⟨d, hd⟩
      exact congrArg Subtype.val this
    calc d * w * c * (d * w)⁻¹ = d * (w * c * w⁻¹) * d⁻¹ := by group
      _ = d * c⁻¹ * d⁻¹ := by rw [h1]
      _ = c⁻¹ := by
        have : d * c⁻¹ = c⁻¹ * d := by
          have h2 := hcomm
          calc d * c⁻¹ = c⁻¹ * (c * d) * c⁻¹ := by group
            _ = c⁻¹ * (d * c) * c⁻¹ := by rw [h2]
            _ = c⁻¹ * d := by group
        rw [this]
        group

end Linear

end CFSG.GH74.Uniqueness.Bender
