module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.IVK

theorem padicValNat_two_two_mul_odd {m : ℕ} (hm : Odd m) : padicValNat 2 (2 * m) = 1 := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [padicValNat.mul h2 hm0, padicValNat.self (by norm_num : 1 < 2)]
  have : ¬ 2 ∣ m := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hm
    omega
  rw [padicValNat.eq_zero_of_not_dvd this]

theorem padicValNat_two_pow_four_sq_sub_one {a : ℕ} (ha : Odd a) (ha1 : 1 < a) :
    padicValNat 2 ((a ^ 4) ^ 2 - 1) = padicValNat 2 (a ^ 2 - 1) + 2 := by
  obtain ⟨k, hk⟩ := ha
  subst hk
  have e1 : ((2 * k + 1) ^ 4) ^ 2 = ((2 * k + 1) ^ 2) ^ 4 := by ring
  rw [e1]
  generalize hb : (2 * k + 1) ^ 2 = b
  have hb8 : b % 8 = 1 := by
    have h : k * (k + 1) % 2 = 0 := by
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩ <;> subst hj <;> ring_nf <;> omega
    have : b = 8 * (k * (k + 1) / 2) + 1 := by
      rw [← hb]
      nlinarith [Nat.div_add_mod (k * (k + 1)) 2]
    omega
  obtain ⟨c, hc⟩ : ∃ c, b = 8 * c + 1 := ⟨b / 8, by omega⟩
  have hb1 : 1 < b := by nlinarith
  have e3 : b ^ 4 - 1 = (b - 1) * ((b + 1) * (b ^ 2 + 1)) := by
    obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [e3]
  have hne1 : b - 1 ≠ 0 := by omega
  have hne2 : (b + 1) * (b ^ 2 + 1) ≠ 0 := by positivity
  rw [padicValNat.mul hne1 hne2, padicValNat.mul (by omega) (by positivity)]
  have hv1 : padicValNat 2 (b + 1) = 1 := by
    have : b + 1 = 2 * (4 * c + 1) := by omega
    rw [this]; exact padicValNat_two_two_mul_odd ⟨2 * c, by omega⟩
  have hv2 : padicValNat 2 (b ^ 2 + 1) = 1 := by
    have : b ^ 2 + 1 = 2 * (32 * c ^ 2 + 8 * c + 1) := by rw [hc]; ring
    rw [this]; exact padicValNat_two_two_mul_odd ⟨16 * c ^ 2 + 4 * c, by omega⟩
  rw [hv1, hv2]

theorem not_two_pow_dvd_of_pow_four {a n : ℕ} (ha : Odd a) (ha1 : 1 < a)
    (hn : n = a ^ 4 * ((a ^ 4) ^ 2 - 1) / 2) :
    ¬ 2 ^ n.factorization 2 ∣ a * (a ^ 2 - 1) := by
  have hq : Odd (a ^ 4) := ha.pow
  have hq1 : 1 < a ^ 4 := Nat.one_lt_pow (by norm_num) ha1
  have hX : 2 ∣ (a ^ 4) ^ 2 - 1 := by
    have : Odd ((a ^ 4) ^ 2) := hq.pow
    have := Nat.odd_iff.mp this
    omega
  have hX0 : (a ^ 4) ^ 2 - 1 ≠ 0 := by
    have : 1 < (a ^ 4) ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have h2n : 2 * n = a ^ 4 * ((a ^ 4) ^ 2 - 1) := by
    rw [hn]
    exact Nat.mul_div_cancel' (dvd_mul_of_dvd_right hX _)
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : a ^ 4 * ((a ^ 4) ^ 2 - 1) = 0 := by omega
    rcases mul_eq_zero.mp this with h | h
    · omega
    · exact hX0 h
  have hv1 : padicValNat 2 (2 * n) = padicValNat 2 n + 1 := by
    rw [padicValNat.mul (by norm_num) hn0, padicValNat.self (by norm_num : 1 < 2)]
    ring
  have hodd0 : padicValNat 2 (a ^ 4) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hq
    omega
  have hodd1 : padicValNat 2 a = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := ha
    omega
  have hv2 : padicValNat 2 (2 * n) = padicValNat 2 ((a ^ 4) ^ 2 - 1) := by
    rw [h2n, padicValNat.mul (by omega) hX0, hodd0, zero_add]
  have hv3 := padicValNat_two_pow_four_sq_sub_one ha ha1
  have ha2 : a ^ 2 - 1 ≠ 0 := by
    have : 1 < a ^ 2 := Nat.one_lt_pow (by norm_num) ha1
    omega
  have hv4 : padicValNat 2 (a * (a ^ 2 - 1)) = padicValNat 2 (a ^ 2 - 1) := by
    rw [padicValNat.mul (by omega) ha2, hodd1, zero_add]
  intro hdvd
  rw [Nat.factorization_def n Nat.prime_two] at hdvd
  have hle := (padicValNat_dvd_iff_le (p := 2) (by
    have : 0 < a * (a ^ 2 - 1) := by
      apply Nat.mul_pos (by omega) (by omega)
    omega)).mp hdvd
  omega

theorem exists_two_part {G : Type*} [Group G] (x : G) (hx : IsOfFinOrder x) :
    ∃ a b : G, a ∈ Subgroup.zpowers x ∧ b ∈ Subgroup.zpowers x ∧ x = a * b ∧
      (∃ k : ℕ, orderOf a = 2 ^ k) ∧ Odd (orderOf b) := by
  have hpos : orderOf x ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_two_left.mpr hm).pow_left k
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨x ^ ((m : ℤ) * v), x ^ (((2 ^ k : ℕ) : ℤ) * u), ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  · rw [← zpow_add]
    have : ((m : ℤ) * v + ((2 ^ k : ℕ) : ℤ) * u) = 1 := by linarith
    rw [this, zpow_one]
  · have h1 : orderOf (x ^ ((m : ℤ) * v)) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul]
      have : ((m : ℤ) * v) * ((2 ^ k : ℕ) : ℤ) = (orderOf x : ℤ) * v := by
        rw [hkm]; push_cast; ring
      rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    exact ⟨j, hj⟩
  · have h1 : orderOf (x ^ (((2 ^ k : ℕ) : ℤ) * u)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul]
      have : (((2 ^ k : ℕ) : ℤ) * u) * (m : ℤ) = (orderOf x : ℤ) * u := by
        rw [hkm]; push_cast; ring
      rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact hm.of_dvd_nat h1

theorem exists_orderOf_four_of_cyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (h4 : 4 ∣ Nat.card G) : ∃ g : G, orderOf g = 4 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf γ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨j, hj⟩ := h4
  have hpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h] at hj
      have := Nat.card_pos (α := G)
      omega
    · exact h
  refine ⟨γ ^ j, ?_⟩
  rw [orderOf_pow' _ (by omega), hord, hj, Nat.gcd_eq_right (Dvd.intro_left 4 rfl),
    Nat.mul_div_cancel _ hpos]

end CFSG.GH74.GLS.IVK
