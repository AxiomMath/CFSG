module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] {x₁ x₂ : G}

private theorem fzc_sy3_mem_closure_pair {x y : G} (hxy : x * y = y * x) {g : G}
    (hg : g ∈ closure ({x, y} : Set G)) : ∃ i j : ℤ, g = x ^ i * y ^ j := by
  induction hg using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with rfl | hw
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul u v _ _ hu hv =>
    obtain ⟨i, j, rfl⟩ := hu
    obtain ⟨k, l, rfl⟩ := hv
    refine ⟨i + k, j + l, ?_⟩
    have hcom : y ^ j * x ^ k = x ^ k * y ^ j :=
      (Commute.zpow_zpow (hxy : Commute x y) k j).eq.symm
    calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
      _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [hcom]
      _ = x ^ (i + k) * y ^ (j + l) := by rw [zpow_add, zpow_add]; group
  | inv u _ hu =>
    obtain ⟨i, j, rfl⟩ := hu
    refine ⟨-i, -j, ?_⟩
    have hcom : y ^ (-j) * x ^ (-i) = x ^ (-i) * y ^ (-j) :=
      (Commute.zpow_zpow (hxy : Commute x y) (-i) (-j)).eq.symm
    calc (x ^ i * y ^ j)⁻¹ = y ^ (-j) * x ^ (-i) := by group
      _ = x ^ (-i) * y ^ (-j) := hcom

private theorem fzc_sy3_zpow_lt {x : G} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) (i : ℤ) :
    ∃ m : ℕ, m < n ∧ x ^ i = x ^ m := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hlt : i % n < n := Int.emod_lt_of_pos i hn'
  have hge : 0 ≤ i % n := Int.emod_nonneg i hn'.ne'
  refine ⟨(i % n).toNat, by omega, ?_⟩
  have h4 : x ^ (n : ℤ) = 1 := by rw [zpow_natCast, hx]
  have hi : i % n + n * (i / n) = i := by have := Int.mul_ediv_add_emod i n; omega
  have hnn : ((i % n).toNat : ℤ) = i % n := Int.toNat_of_nonneg hge
  calc x ^ i = x ^ (i % n + (n : ℤ) * (i / n)) := by rw [hi]
    _ = x ^ (i % n) := by rw [zpow_add, zpow_mul, h4, one_zpow, mul_one]
    _ = x ^ (i % n).toNat := by rw [← zpow_natCast, hnn]

private theorem fzc_sy3_pow_mod {x : G} (hx : x ^ 4 = 1) (n : ℕ) : x ^ n = x ^ (n % 4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, hx, one_pow, mul_one]

theorem fzc_sy3_coord (hc : x₁ * x₂ = x₂ * x₁) (h₁ : orderOf x₁ = 4) (h₂ : orderOf x₂ = 4)
    {e : G} (he : e ∈ baseGrp x₁ x₂) : ∃ i j : ℕ, i < 4 ∧ j < 4 ∧ e = x₁ ^ i * x₂ ^ j := by
  obtain ⟨i, j, rfl⟩ := fzc_sy3_mem_closure_pair hc he
  have e₁ : x₁ ^ 4 = 1 := by rw [← h₁]; exact pow_orderOf_eq_one x₁
  have e₂ : x₂ ^ 4 = 1 := by rw [← h₂]; exact pow_orderOf_eq_one x₂
  obtain ⟨m, hm, hm'⟩ := fzc_sy3_zpow_lt (by norm_num) e₁ i
  obtain ⟨n, hn, hn'⟩ := fzc_sy3_zpow_lt (by norm_num) e₂ j
  exact ⟨m, n, hm, hn, by rw [hm', hn']⟩

theorem fzc_sy3_coord_eq (h₁ : orderOf x₁ = 4) (h₂ : orderOf x₂ = 4)
    (hinf : zpowers x₁ ⊓ zpowers x₂ = ⊥) {i j k l : ℕ} :
    x₁ ^ i * x₂ ^ j = x₁ ^ k * x₂ ^ l ↔ i % 4 = k % 4 ∧ j % 4 = l % 4 := by
  have e₁ : x₁ ^ 4 = 1 := by rw [← h₁]; exact pow_orderOf_eq_one x₁
  have e₂ : x₂ ^ 4 = 1 := by rw [← h₂]; exact pow_orderOf_eq_one x₂
  constructor
  · intro h
    have hL : x₁ ^ (3 * k) * (x₁ ^ i * x₂ ^ j) * x₂ ^ (3 * j) = x₁ ^ (i + 3 * k) := by
      calc x₁ ^ (3 * k) * (x₁ ^ i * x₂ ^ j) * x₂ ^ (3 * j)
          = x₁ ^ (3 * k + i) * x₂ ^ (4 * j) := by
            rw [pow_add, show 4 * j = j + 3 * j by ring, pow_add x₂ j]; group
        _ = x₁ ^ (i + 3 * k) := by rw [pow_mul, e₂, one_pow, mul_one, Nat.add_comm]
    have hR : x₁ ^ (3 * k) * (x₁ ^ k * x₂ ^ l) * x₂ ^ (3 * j) = x₂ ^ (l + 3 * j) := by
      calc x₁ ^ (3 * k) * (x₁ ^ k * x₂ ^ l) * x₂ ^ (3 * j)
          = x₁ ^ (4 * k) * x₂ ^ (l + 3 * j) := by
            rw [show 4 * k = 3 * k + k by ring, pow_add, pow_add x₂ l]; group
        _ = x₂ ^ (l + 3 * j) := by rw [pow_mul, e₁, one_pow, one_mul]
    have hkey : x₁ ^ (i + 3 * k) = x₂ ^ (l + 3 * j) := by rw [← hL, ← hR, h]
    have hmem : x₁ ^ (i + 3 * k) ∈ zpowers x₁ ⊓ zpowers x₂ := by
      refine ⟨pow_mem (mem_zpowers x₁) _, ?_⟩
      rw [hkey]
      exact pow_mem (mem_zpowers x₂) _
    rw [hinf, mem_bot] at hmem
    have hmem' : x₂ ^ (l + 3 * j) = 1 := by rw [← hkey, hmem]
    have d₁ : 4 ∣ i + 3 * k := by rw [← h₁]; exact orderOf_dvd_of_pow_eq_one hmem
    have d₂ : 4 ∣ l + 3 * j := by rw [← h₂]; exact orderOf_dvd_of_pow_eq_one hmem'
    omega
  · rintro ⟨hi, hj⟩
    rw [fzc_sy3_pow_mod e₁ i, fzc_sy3_pow_mod e₂ j, fzc_sy3_pow_mod e₁ k,
      fzc_sy3_pow_mod e₂ l, hi, hj]

theorem fzc_sy3_mem_fourGrp (hc : x₁ * x₂ = x₂ * x₁) (h₁ : orderOf x₁ = 4)
    (h₂ : orderOf x₂ = 4) {g : G} :
    g ∈ fourGrp x₁ x₂ ↔ ∃ i j : ℕ, i < 2 ∧ j < 2 ∧ g = x₁ ^ (2 * i) * x₂ ^ (2 * j) := by
  have e₁ : x₁ ^ 4 = 1 := by rw [← h₁]; exact pow_orderOf_eq_one x₁
  have e₂ : x₂ ^ 4 = 1 := by rw [← h₂]; exact pow_orderOf_eq_one x₂
  have hcom : Commute x₁ x₂ := hc
  have hz : (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := hcom.mul_pow 2
  have hy : x₂ ^ 2 = (x₁ ^ 2)⁻¹ * (x₁ * x₂) ^ 2 := by rw [hz]; group
  have h2a : ∀ a : ℕ, x₁ ^ (2 * a) = x₁ ^ (2 * (a % 2)) := by
    intro a
    rw [fzc_sy3_pow_mod e₁ (2 * a), fzc_sy3_pow_mod e₁ (2 * (a % 2))]
    congr 1
    omega
  have h2b : ∀ a : ℕ, x₂ ^ (2 * a) = x₂ ^ (2 * (a % 2)) := by
    intro a
    rw [fzc_sy3_pow_mod e₂ (2 * a), fzc_sy3_pow_mod e₂ (2 * (a % 2))]
    congr 1
    omega
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with rfl | hw
      · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ⟨1, 1, by norm_num, by norm_num, by rw [hz]⟩
    | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨i, j, -, -, rfl⟩ := hu
      obtain ⟨k, l, -, -, rfl⟩ := hv
      refine ⟨(i + k) % 2, (j + l) % 2, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
        ?_⟩
      rw [← h2a, ← h2b, mul_add, mul_add, pow_add, pow_add]
      have hcm : x₂ ^ (2 * j) * x₁ ^ (2 * k) = x₁ ^ (2 * k) * x₂ ^ (2 * j) :=
        ((hcom.pow_pow (2 * k) (2 * j)).eq).symm
      calc x₁ ^ (2 * i) * x₂ ^ (2 * j) * (x₁ ^ (2 * k) * x₂ ^ (2 * l))
          = x₁ ^ (2 * i) * (x₂ ^ (2 * j) * x₁ ^ (2 * k)) * x₂ ^ (2 * l) := by group
        _ = x₁ ^ (2 * i) * (x₁ ^ (2 * k) * x₂ ^ (2 * j)) * x₂ ^ (2 * l) := by rw [hcm]
        _ = x₁ ^ (2 * i) * x₁ ^ (2 * k) * (x₂ ^ (2 * j) * x₂ ^ (2 * l)) := by group
    | inv u _ hu =>
      obtain ⟨i, j, hi, hj, rfl⟩ := hu
      refine ⟨i, j, hi, hj, ?_⟩
      have hi2 : (x₁ ^ (2 * i))⁻¹ = x₁ ^ (2 * i) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 * i + 2 * i = 4 * i by ring, pow_mul, e₁,
          one_pow]
      have hj2 : (x₂ ^ (2 * j))⁻¹ = x₂ ^ (2 * j) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 * j + 2 * j = 4 * j by ring, pow_mul, e₂,
          one_pow]
      rw [mul_inv_rev, hi2, hj2]
      exact ((hcom.pow_pow (2 * i) (2 * j)).eq).symm
  · rintro ⟨i, j, -, -, rfl⟩
    refine mul_mem ?_ ?_
    · rw [pow_mul]
      exact pow_mem (subset_closure (by simp)) i
    · rw [pow_mul, hy]
      exact pow_mem (mul_mem (inv_mem (subset_closure (by simp)))
        (subset_closure (by simp))) j

end CFSG.OddStandard.SmallF3.FritzII
