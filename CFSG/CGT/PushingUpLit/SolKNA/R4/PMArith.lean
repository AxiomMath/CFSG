module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMBasic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

section Cyclic

variable {G : Type*} [Group G]

theorem exists_pow_not_mem_mul_self_mem (H : Subgroup G) {a : G} {m : ℕ} (ha : a ^ 2 ^ m = 1)
    (haH : a ∉ H) : ∃ j : ℕ, a ^ 2 ^ j ∉ H ∧ a ^ 2 ^ j * a ^ 2 ^ j ∈ H := by
  induction m generalizing a with
  | zero =>
    have h1 : a = 1 := by simpa using ha
    exact absurd (h1 ▸ H.one_mem) haH
  | succ m ih =>
    by_cases h2 : a * a ∈ H
    · exact ⟨0, by simpa using haH, by simpa using h2⟩
    · have ha2 : (a * a) ^ 2 ^ m = 1 := by
        rw [← sq, ← pow_mul, ← pow_succ']
        exact ha
      obtain ⟨j, hj1, hj2⟩ := ih ha2 h2
      have e : a ^ 2 ^ (j + 1) = (a * a) ^ 2 ^ j := by
        rw [pow_succ', pow_mul, sq]
      refine ⟨j + 1, by rw [e]; exact hj1, by rw [e]; exact hj2⟩

theorem forall_zpow_iff_dvd {u y : G} {α : ℤ} (hyu : y * u * y⁻¹ = u ^ α) (ε : ℤ) :
    (∀ x ∈ Subgroup.zpowers u, y * x * y⁻¹ = x ^ ε) ↔ (orderOf u : ℤ) ∣ α - ε := by
  have key : (orderOf u : ℤ) ∣ α - ε ↔ u ^ α = u ^ ε := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, mul_inv_eq_one]
  rw [key]
  constructor
  · intro h
    rw [← hyu]
    exact h u (Subgroup.mem_zpowers u)
  · intro h x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hyu, h, ← zpow_mul, ← zpow_mul, mul_comm]

theorem actsPM_zpowers_iff {u g : G} {α : ℤ} (h : g * u * g⁻¹ = u ^ α) :
    ActsPM (Subgroup.zpowers u) g ↔ (orderOf u : ℤ) ∣ α - 1 ∨ (orderOf u : ℤ) ∣ α + 1 := by
  unfold ActsPM
  have h1 := forall_zpow_iff_dvd h 1
  have h2 := forall_zpow_iff_dvd h (-1)
  simp only [zpow_one, zpow_neg_one, sub_neg_eq_add] at h1 h2
  rw [h1, h2]

private theorem exists_generator_zpowers {U : Subgroup G} (hU : IsCyclic ↥U) {n : ℕ}
    (hUn : Nat.card ↥U = 2 ^ n) : ∃ u : G, U = Subgroup.zpowers u ∧ orderOf u = 2 ^ n := by
  obtain ⟨c, hc⟩ := (IsCyclic.exists_generator : ∃ c : ↥U, ∀ x : ↥U, x ∈ Subgroup.zpowers c)
  have htop : Subgroup.zpowers c = ⊤ := eq_top_iff.mpr fun x _ => hc x
  have hord : orderOf c = 2 ^ n := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hUn]
  refine ⟨(c : G), ?_, by rw [Subgroup.orderOf_coe, hord]⟩
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩
  · intro hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hj]
    exact Subgroup.zpow_mem U c.2 j

private theorem odd_geom_sum (α : ℤ) {k : ℕ} (hk : Odd k) :
    Odd (∑ i ∈ Finset.range k, α ^ i) := by
  rw [Int.odd_iff]
  rcases Int.even_or_odd α with hα | hα
  · obtain ⟨r, hr⟩ := hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have key : ∀ j : ℕ, (∑ i ∈ Finset.range (j + 1), α ^ i) % 2 = 1 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Finset.sum_range_succ]
        have h2 : α ^ (j + 1) % 2 = 0 := Int.even_iff.mp (Int.even_pow.mpr ⟨hα, Nat.succ_ne_zero j⟩)
        omega
    exact key j
  · have key : ∀ j : ℕ, (∑ i ∈ Finset.range j, α ^ i) % 2 = (j : ℤ) % 2 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Finset.sum_range_succ]
        have h2 : α ^ j % 2 = 1 := Int.odd_iff.mp hα.pow
        omega
    rw [key k]
    obtain ⟨r, hr⟩ := hk
    omega

theorem mem_centralizer_of_odd_orderOf {D : Subgroup G} (hDc : IsCyclic ↥D) {m : ℕ}
    (hDn : Nat.card ↥D = 2 ^ m) {n : G} (hn : n ∈ Subgroup.normalizer (D : Set G))
    (hodd : Odd (orderOf n)) : n ∈ Subgroup.centralizer (D : Set G) := by
  obtain ⟨u, hDu, hord⟩ := exists_generator_zpowers hDc hDn
  have huD : u ∈ D := by rw [hDu]; exact Subgroup.mem_zpowers u
  have hnu : n * u * n⁻¹ ∈ Subgroup.zpowers u := by
    rw [← hDu]; exact (Subgroup.mem_normalizer_iff.mp hn u).mp huD
  obtain ⟨α, hα⟩ := Subgroup.mem_zpowers_iff.mp hnu
  have hα' : n * u * n⁻¹ = u ^ α := hα.symm
  have hconj : ∀ j : ℕ, n ^ j * u * (n ^ j)⁻¹ = u ^ (α ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : n ^ (j + 1) * u * (n ^ (j + 1))⁻¹ = n * (n ^ j * u * (n ^ j)⁻¹) * n⁻¹ := by
        rw [pow_succ']; group
      rw [e1, ih, ← conj_zpow, hα', ← zpow_mul, pow_succ']
  have hpow : (orderOf u : ℤ) ∣ α ^ orderOf n - 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    have h1 := hconj (orderOf n)
    rw [pow_orderOf_eq_one n, one_mul, inv_one, mul_one] at h1
    rw [zpow_sub, zpow_one, ← h1, mul_inv_cancel]
  have hS : (orderOf u : ℤ) ∣ (∑ i ∈ Finset.range (orderOf n), α ^ i) * (α - 1) := by
    rw [geom_sum_mul]; exact hpow
  have hco : IsCoprime (orderOf u : ℤ) (∑ i ∈ Finset.range (orderOf n), α ^ i) := by
    obtain ⟨c, hc⟩ := odd_geom_sum α hodd
    rw [hord]
    push_cast
    exact IsCoprime.pow_left ⟨-c, 1, by rw [hc]; ring⟩
  have hαu : (orderOf u : ℤ) ∣ α - 1 := hco.dvd_of_dvd_mul_left hS
  have hcentr := (forall_zpow_iff_dvd hα' 1).mpr hαu
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhz : h ∈ Subgroup.zpowers u := by rw [← hDu]; exact hh
  have h1 := hcentr h hhz
  rw [zpow_one] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

theorem exists_mul_eq_isPGroup_odd [Finite G] (n : G) :
    ∃ a b : G, n = a * b ∧ a ∈ Subgroup.zpowers n ∧ b ∈ Subgroup.zpowers n ∧
      IsPGroup 2 ↥(Subgroup.zpowers a) ∧ Odd (orderOf b) := by
  obtain ⟨e, k, hk, hnk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have hcop : IsCoprime ((2 ^ e : ℕ) : ℤ) (k : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hk)
  obtain ⟨s, t, hst⟩ := hcop
  push_cast at hst
  refine ⟨n ^ (t * (k : ℤ)), n ^ (s * 2 ^ e), ?_, Subgroup.zpow_mem_zpowers n _,
    Subgroup.zpow_mem_zpowers n _, ?_, ?_⟩
  · rw [← zpow_add, show t * (k : ℤ) + s * 2 ^ e = 1 by linear_combination hst, zpow_one]
  · have ha : (n ^ (t * (k : ℤ))) ^ (2 ^ e) = 1 := by
      rw [← zpow_natCast (n ^ (t * (k : ℤ))) (2 ^ e), ← zpow_mul]
      have h1 : t * (k : ℤ) * ((2 ^ e : ℕ) : ℤ) = t * (orderOf n : ℤ) := by
        rw [hnk]; push_cast; ring
      rw [h1, mul_comm (t : ℤ), zpow_mul, zpow_natCast n (orderOf n), pow_orderOf_eq_one, one_zpow]
    rw [IsPGroup.iff_orderOf]
    intro g
    have hdiv : orderOf (g : G) ∣ 2 ^ e :=
      (orderOf_dvd_of_mem_zpowers g.2).trans (orderOf_dvd_of_pow_eq_one ha)
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    exact ⟨i, (Subgroup.orderOf_coe g).symm.trans hi⟩
  · have hb : (n ^ (s * 2 ^ e)) ^ k = 1 := by
      rw [← zpow_natCast (n ^ (s * 2 ^ e)) k, ← zpow_mul]
      have h1 : s * (2 : ℤ) ^ e * (k : ℤ) = s * (orderOf n : ℤ) := by
        rw [hnk]; push_cast; ring
      rw [h1, mul_comm (s : ℤ), zpow_mul, zpow_natCast n (orderOf n), pow_orderOf_eq_one,
        one_zpow]
    exact Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one hb)

end Cyclic

section Integers

private theorem two_pow_dvd_sub_or_add_aux {m : ℕ} {k : ℤ}
    (h : (2 : ℤ) ^ (m + 2) ∣ k ^ 2 - 1) :
    (2 : ℤ) ^ (m + 1) ∣ k - 1 ∨ (2 : ℤ) ^ (m + 1) ∣ k + 1 := by
  obtain ⟨c, hc⟩ := h
  rcases Int.even_or_odd k with ⟨b, rfl⟩ | ⟨a, rfl⟩
  · exfalso
    have e1 : (b + b) ^ 2 - 1 = 2 * (2 * b * b - 1) + 1 := by ring
    have e2 : (2 : ℤ) ^ (m + 2) * c = 2 * (2 ^ (m + 1) * c) := by ring
    rw [e1, e2] at hc
    generalize 2 * b * b - 1 = B at hc
    generalize (2 : ℤ) ^ (m + 1) * c = M at hc
    omega
  · have hm' : a * (a + 1) = 2 ^ m * c := by
      have h4 : (4 : ℤ) * (a * (a + 1)) = 4 * (2 ^ m * c) := by
        rw [show (4 : ℤ) * (a * (a + 1)) = (2 * a + 1) ^ 2 - 1 by ring, hc]
        ring
      exact mul_left_cancel₀ (by norm_num) h4
    rcases Int.even_or_odd a with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · left
      have hco : IsCoprime ((2 : ℤ) ^ m) (d + d + 1) := IsCoprime.pow_left ⟨-d, 1, by ring⟩
      have hdvd : (2 : ℤ) ^ m ∣ (d + d) * (d + d + 1) := ⟨c, hm'⟩
      obtain ⟨e, he⟩ := hco.dvd_of_dvd_mul_right hdvd
      exact ⟨e, by rw [pow_succ]; linear_combination 2 * he⟩
    · right
      have hco : IsCoprime ((2 : ℤ) ^ m) (2 * d + 1) := IsCoprime.pow_left ⟨-d, 1, by ring⟩
      have hdvd : (2 : ℤ) ^ m ∣ (2 * d + 1 + 1) * (2 * d + 1) := ⟨c, by rw [← hm']; ring⟩
      obtain ⟨e, he⟩ := hco.dvd_of_dvd_mul_right hdvd
      exact ⟨e, by rw [pow_succ]; linear_combination 2 * he⟩

theorem not_two_pow_dvd_sq_add_one {n : ℕ} (hn : 2 ≤ n) (α : ℤ) : ¬ (2 : ℤ) ^ n ∣ α ^ 2 + 1 := by
  intro h
  have h4 : (4 : ℤ) ∣ α ^ 2 + 1 := by
    have h4n : (4 : ℤ) ∣ 2 ^ n := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 hn
    exact h4n.trans h
  have hmod : (α ^ 2 + 1) % 4 = 0 := Int.emod_eq_zero_of_dvd h4
  rw [pow_two, Int.add_emod, Int.mul_emod] at hmod
  have hcases : α % 4 = 0 ∨ α % 4 = 1 ∨ α % 4 = 2 ∨ α % 4 = 3 := by omega
  rcases hcases with h0 | h0 | h0 | h0 <;> rw [h0] at hmod <;> norm_num at hmod

theorem four_cases_of_two_pow_dvd_sq_sub_one {n : ℕ} (hn : 3 ≤ n) {α : ℤ}
    (h : (2 : ℤ) ^ n ∣ α ^ 2 - 1) :
    (2 : ℤ) ^ n ∣ α - 1 ∨ (2 : ℤ) ^ n ∣ α + 1 ∨ (2 : ℤ) ^ n ∣ α - (1 + 2 ^ (n - 1)) ∨
      (2 : ℤ) ^ n ∣ α + (1 + 2 ^ (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hn1 : m + 2 - 1 = m + 1 := by omega
  rw [hn1]
  rcases two_pow_dvd_sub_or_add_aux h with ⟨r, hr⟩ | ⟨r, hr⟩
  · rcases Int.even_or_odd r with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨j, by linear_combination hr⟩
    · exact Or.inr (Or.inr (Or.inl ⟨j, by linear_combination hr⟩))
  · rcases Int.even_or_odd r with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inr (Or.inl ⟨j, by linear_combination hr⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨j + 1, by linear_combination hr⟩))

private theorem two_pow_dvd_mul_pm {n : ℕ} (hn : 3 ≤ n) {α β : ℤ}
    (hα : (2 : ℤ) ^ n ∣ α - (1 + 2 ^ (n - 1)) ∨ (2 : ℤ) ^ n ∣ α + (1 + 2 ^ (n - 1)))
    (hβ : (2 : ℤ) ^ n ∣ β - (1 + 2 ^ (n - 1)) ∨ (2 : ℤ) ^ n ∣ β + (1 + 2 ^ (n - 1))) :
    (2 : ℤ) ^ n ∣ α * β - 1 ∨ (2 : ℤ) ^ n ∣ α * β + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  rw [e1] at hα hβ
  rcases hα with ⟨p, hp⟩ | ⟨p, hp⟩ <;> rcases hβ with ⟨q, hq⟩ | ⟨q, hq⟩
  · obtain rfl : α = 1 + 2 ^ (k + 1) + 2 ^ (k + 2) * p := by linear_combination hp
    obtain rfl : β = 1 + 2 ^ (k + 1) + 2 ^ (k + 2) * q := by linear_combination hq
    exact Or.inl ⟨1 + 2 ^ k + (1 + 2 ^ (k + 1)) * (p + q) + 2 ^ (k + 2) * p * q, by ring⟩
  · obtain rfl : α = 1 + 2 ^ (k + 1) + 2 ^ (k + 2) * p := by linear_combination hp
    obtain rfl : β = -(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * q := by linear_combination hq
    exact Or.inr ⟨-(1 + 2 ^ k) + (1 + 2 ^ (k + 1)) * (q - p) + 2 ^ (k + 2) * p * q, by ring⟩
  · obtain rfl : α = -(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * p := by linear_combination hp
    obtain rfl : β = 1 + 2 ^ (k + 1) + 2 ^ (k + 2) * q := by linear_combination hq
    exact Or.inr ⟨-(1 + 2 ^ k) + (1 + 2 ^ (k + 1)) * (p - q) + 2 ^ (k + 2) * p * q, by ring⟩
  · obtain rfl : α = -(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * p := by linear_combination hp
    obtain rfl : β = -(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * q := by linear_combination hq
    exact Or.inl ⟨1 + 2 ^ k - (1 + 2 ^ (k + 1)) * (p + q) + 2 ^ (k + 2) * p * q, by ring⟩

theorem exists_int_solve {n : ℕ} (hn : 3 ≤ n) {α m : ℤ}
    (hα : (2 : ℤ) ^ n ∣ α - (1 + 2 ^ (n - 1)) ∨ (2 : ℤ) ^ n ∣ α + (1 + 2 ^ (n - 1)))
    (hm : (2 : ℤ) ^ n ∣ m * (α - 1)) : ∃ i : ℤ, (2 : ℤ) ^ n ∣ i * (α + 1) + m := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  rw [e1] at hα
  obtain ⟨t, ht⟩ := hm
  rcases hα with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain rfl : α = 1 + 2 ^ (k + 2) + 2 ^ (k + 3) * r := by linear_combination hr
    have hmo : m * (1 + 2 * r) = 2 * t := by
      have h4 : (2 : ℤ) ^ (k + 2) * (m * (1 + 2 * r)) = 2 ^ (k + 2) * (2 * t) := by
        linear_combination ht
      exact mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) h4
    obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨t - r * m, by linear_combination hmo⟩
    exact ⟨-(1 + 2 ^ (k + 1) + 2 ^ (k + 2) * r) * m',
      -m' * ((1 + 2 * r) + 2 ^ k * (1 + 2 * r) ^ 2), by ring⟩
  · have hw : α - 1 = 2 * (-(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * r) := by linear_combination hr
    have hmw : m * (-(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * r) = 2 ^ (k + 2) * t := by
      have h4 : (2 : ℤ) * (m * (-(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * r)) =
          2 * (2 ^ (k + 2) * t) := by
        linear_combination ht - m * hw
      exact mul_left_cancel₀ two_ne_zero h4
    have hco : IsCoprime ((2 : ℤ) ^ (k + 2)) (-(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * r) :=
      IsCoprime.pow_left ⟨-(2 ^ k) + 2 ^ (k + 1) * r, -1, by ring⟩
    have hdvd : (2 : ℤ) ^ (k + 2) ∣ m * (-(1 + 2 ^ (k + 1)) + 2 ^ (k + 2) * r) := ⟨t, hmw⟩
    obtain ⟨s, hs⟩ := hco.dvd_of_dvd_mul_right hdvd
    obtain rfl : m = 2 ^ (k + 2) * s := hs
    exact ⟨s, s * r, by linear_combination s * hr⟩

end Integers

section Action

variable {G : Type*} [Group G]

private theorem exists_mul_of_mem_sup {U V : Subgroup G}
    (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) {m : G} (hm : m ∈ U ⊔ V) :
    ∃ u ∈ U, ∃ v ∈ V, m = u * v := by
  let T : Subgroup G :=
    { carrier := {m | ∃ u ∈ U, ∃ v ∈ V, m = u * v}
      one_mem' := ⟨1, U.one_mem, 1, V.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨u₁, hu₁, v₁, hv₁, rfl⟩ ⟨u₂, hu₂, v₂, hv₂, rfl⟩
        refine ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, v₁ * v₂, V.mul_mem hv₁ hv₂, ?_⟩
        calc u₁ * v₁ * (u₂ * v₂) = u₁ * (v₁ * u₂) * v₂ := by group
          _ = u₁ * (u₂ * v₁) * v₂ := by rw [hc u₂ hu₂ v₁ hv₁]
          _ = u₁ * u₂ * (v₁ * v₂) := by group
      inv_mem' := by
        rintro _ ⟨u, hu, v, hv, rfl⟩
        refine ⟨u⁻¹, U.inv_mem hu, v⁻¹, V.inv_mem hv, ?_⟩
        rw [mul_inv_rev]
        exact (Commute.inv_inv (show Commute u v from hc u hu v hv)).eq.symm }
  have hle : U ⊔ V ≤ T := by
    refine sup_le ?_ ?_
    · intro u hu
      exact ⟨u, hu, 1, V.one_mem, (mul_one u).symm⟩
    · intro v hv
      exact ⟨1, U.one_mem, v, hv, (one_mul v).symm⟩
  obtain ⟨u, hu, v, hv, h⟩ := hle hm
  exact ⟨u, hu, v, hv, h⟩

theorem exists_exponent_of_actsPM_sq {u a : G} {n : ℕ} (hn : 3 ≤ n) (hu : orderOf u = 2 ^ n)
    (hau : a * u * a⁻¹ ∈ Subgroup.zpowers u) (ha2 : ActsPM (Subgroup.zpowers u) (a * a))
    (ha : ¬ ActsPM (Subgroup.zpowers u) a) :
    ∃ α : ℤ, a * u * a⁻¹ = u ^ α ∧
      ((2 : ℤ) ^ n ∣ α - (1 + 2 ^ (n - 1)) ∨ (2 : ℤ) ^ n ∣ α + (1 + 2 ^ (n - 1))) := by
  obtain ⟨α, hα⟩ := Subgroup.mem_zpowers_iff.mp hau
  have hαe : a * u * a⁻¹ = u ^ α := hα.symm
  have hd : ((orderOf u : ℕ) : ℤ) = (2 : ℤ) ^ n := by rw [hu]; norm_num
  have hsq : a * a * u * (a * a)⁻¹ = u ^ (α * α) := by
    calc a * a * u * (a * a)⁻¹ = a * (a * u * a⁻¹) * a⁻¹ := by group
      _ = a * u ^ α * a⁻¹ := by rw [hαe]
      _ = (a * u * a⁻¹) ^ α := by rw [← conj_zpow]
      _ = (u ^ α) ^ α := by rw [hαe]
      _ = u ^ (α * α) := (zpow_mul u α α).symm
  have h2 := (actsPM_zpowers_iff hsq).mp ha2
  rw [hd] at h2
  have h1 : (2 : ℤ) ^ n ∣ α ^ 2 - 1 := by
    rcases h2 with h | h
    · rw [sq]; exact h
    · have h' : (2 : ℤ) ^ n ∣ α ^ 2 + 1 := by rw [sq]; exact h
      exact (not_two_pow_dvd_sq_add_one (n := n) (by omega) α h').elim
  rcases four_cases_of_two_pow_dvd_sq_sub_one hn h1 with h | h | h | h
  · exact absurd ((actsPM_zpowers_iff hαe).mpr (Or.inl (by rw [hd]; exact h))) ha
  · exact absurd ((actsPM_zpowers_iff hαe).mpr (Or.inr (by rw [hd]; exact h))) ha
  · exact ⟨α, hαe, Or.inl h⟩
  · exact ⟨α, hαe, Or.inr h⟩

theorem conj_eq_mul_pow_or {u a : G} {n : ℕ} (hn : 3 ≤ n) (hu : orderOf u = 2 ^ n)
    (hau : a * u * a⁻¹ ∈ Subgroup.zpowers u) (ha2 : a * a = 1)
    (ha : ¬ ActsPM (Subgroup.zpowers u) a) :
    a * u * a⁻¹ = u ^ 2 ^ (n - 1) * u ∨ a * u * a⁻¹ = u ^ 2 ^ (n - 1) * u⁻¹ := by
  obtain ⟨α, hαe, hα⟩ := exists_exponent_of_actsPM_sq hn hu hau
    (by rw [ha2]; exact actsPM_one _) ha
  have hd : ((orderOf u : ℕ) : ℤ) = (2 : ℤ) ^ n := by rw [hu]; norm_num
  have hdiv : ∀ e : ℤ, (2 : ℤ) ^ n ∣ e → u ^ e = 1 := fun e he =>
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [hd]; exact he)
  have h2n : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  have hz2 : u ^ (2 ^ (n - 1)) * u ^ (2 ^ (n - 1)) = 1 := by
    rw [← pow_add, h2n, ← hu]
    exact pow_orderOf_eq_one u
  have hzinv : (u ^ (2 ^ (n - 1)))⁻¹ = u ^ (2 ^ (n - 1)) := inv_eq_of_mul_eq_one_right hz2
  have hzp : u ^ ((2 : ℤ) ^ (n - 1)) = u ^ (2 ^ (n - 1)) := by
    rw [← zpow_natCast u (2 ^ (n - 1)), Nat.cast_pow, Nat.cast_ofNat]
  have hX : u ^ (1 + (2 : ℤ) ^ (n - 1)) = u ^ (2 ^ (n - 1)) * u := by
    rw [show (1 + (2 : ℤ) ^ (n - 1)) = (2 : ℤ) ^ (n - 1) + 1 by ring, zpow_add, zpow_one, hzp]
  rcases hα with h | h
  · left
    have e1 : u ^ (α - (1 + 2 ^ (n - 1))) = 1 := hdiv _ h
    rw [zpow_sub, mul_inv_eq_one] at e1
    rw [hαe, e1, hX]
  · right
    have e2 : u ^ α * u ^ (1 + (2 : ℤ) ^ (n - 1)) = 1 := by
      rw [← zpow_add]; exact hdiv _ h
    have hc : Commute (u ^ (2 ^ (n - 1))) u⁻¹ := ((Commute.refl u).pow_left _).inv_right
    rw [hαe, eq_inv_of_mul_eq_one_left e2, hX, mul_inv_rev, hzinv, hc.eq.symm]

theorem inv_mul_mem_pmSubgroup_of_involution {U : Subgroup G} (hU : IsCyclic ↥U) {n : ℕ}
    (hn : 3 ≤ n) (hUn : Nat.card ↥U = 2 ^ n) {x b : G}
    (hx : x ∈ Subgroup.normalizer (U : Set G)) (hb : b ∈ Subgroup.normalizer (U : Set G))
    (hx2 : x * x = 1) (hb2 : b * b = 1) (hxU : ¬ ActsPM U x) (hbU : ¬ ActsPM U b) :
    x⁻¹ * b ∈ pmSubgroup U := by
  obtain ⟨u, rfl, hu⟩ := exists_generator_zpowers hU hUn
  have hux : x * u * x⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp hx u).mp (Subgroup.mem_zpowers u)
  have hub : b * u * b⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp hb u).mp (Subgroup.mem_zpowers u)
  obtain ⟨α, hαx, hα⟩ := exists_exponent_of_actsPM_sq hn hu hux
    (by rw [hx2]; exact actsPM_one _) hxU
  obtain ⟨β, hβb, hβ⟩ := exists_exponent_of_actsPM_sq hn hu hub
    (by rw [hb2]; exact actsPM_one _) hbU
  have hxb : x * b * u * (x * b)⁻¹ = u ^ (α * β) := by
    calc x * b * u * (x * b)⁻¹ = x * (b * u * b⁻¹) * x⁻¹ := by group
      _ = x * u ^ β * x⁻¹ := by rw [hβb]
      _ = (x * u * x⁻¹) ^ β := by rw [← conj_zpow]
      _ = (u ^ α) ^ β := by rw [hαx]
      _ = u ^ (α * β) := (zpow_mul u α β).symm
  have hd : ((orderOf u : ℕ) : ℤ) = (2 : ℤ) ^ n := by rw [hu]; norm_num
  have hact : ActsPM (Subgroup.zpowers u) (x * b) :=
    (actsPM_zpowers_iff hxb).mpr (by rw [hd]; exact two_pow_dvd_mul_pm hn hα hβ)
  rw [inv_eq_of_mul_eq_one_right hx2, mem_pmSubgroup]
  exact hact

theorem exists_mul_mul_eq_one {W U V : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hU : IsCyclic ↥U)
    (hV : IsCyclic ↥V) (hUn : Nat.card ↥U = 2 ^ n) (hVn : Nat.card ↥V = 2 ^ n)
    (hUV : U ⊓ V = ⊥) (hW : W = U ⊔ V) (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {a : G}
    {α : ℤ} (hα : (2 : ℤ) ^ n ∣ α - (1 + 2 ^ (n - 1)) ∨ (2 : ℤ) ^ n ∣ α + (1 + 2 ^ (n - 1)))
    (haW : ∀ w ∈ W, a * w * a⁻¹ = w ^ α) (ha2 : a * a ∈ W) :
    ∃ w ∈ W, (a * w) * (a * w) = 1 := by
  obtain ⟨x, rfl, hx⟩ := exists_generator_zpowers hU hUn
  obtain ⟨y, rfl, hy⟩ := exists_generator_zpowers hV hVn
  have hxW : x ∈ W := by rw [hW]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyW : y ∈ W := by rw [hW]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hcxy : Commute x y := hcomm x hxW y hyW
  have hdx : ((orderOf x : ℕ) : ℤ) = (2 : ℤ) ^ n := by rw [hx]; norm_num
  have hdy : ((orderOf y : ℕ) : ℤ) = (2 : ℤ) ^ n := by rw [hy]; norm_num
  have hc : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers y, u * v = v * u :=
    fun u hu v hv => hcomm u (by rw [hW]; exact Subgroup.mem_sup_left hu) v
      (by rw [hW]; exact Subgroup.mem_sup_right hv)
  have hm : a * a ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by rw [← hW]; exact ha2
  obtain ⟨u, hu, v, hv, hmuv⟩ := exists_mul_of_mem_sup hc hm
  obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨q, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hm1 : (a * a) ^ (α - 1) = 1 := by
    have h1 : a * (a * a) * a⁻¹ = a * a := by group
    have h2 := haW (a * a) ha2
    rw [h1] at h2
    rw [zpow_sub_one, ← h2, mul_inv_cancel]
  have hsplit : (x ^ p) ^ (α - 1) * (y ^ q) ^ (α - 1) = 1 := by
    rw [← (hcxy.zpow_zpow p q).mul_zpow (α - 1), ← hmuv, hm1]
  have hx1 : (x ^ p) ^ (α - 1) = 1 := by
    have hex : (x ^ p) ^ (α - 1) ∈ Subgroup.zpowers x := by
      rw [← zpow_mul]; exact Subgroup.zpow_mem_zpowers x _
    have hfy : (y ^ q) ^ (α - 1) ∈ Subgroup.zpowers y := by
      rw [← zpow_mul]; exact Subgroup.zpow_mem_zpowers y _
    have hey : (x ^ p) ^ (α - 1) ∈ Subgroup.zpowers y := by
      rw [eq_inv_of_mul_eq_one_left hsplit]; exact inv_mem hfy
    have hbot : (x ^ p) ^ (α - 1) ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y := ⟨hex, hey⟩
    rw [hUV, Subgroup.mem_bot] at hbot
    exact hbot
  have hy1 : (y ^ q) ^ (α - 1) = 1 := by
    rw [hx1, one_mul] at hsplit
    exact hsplit
  have hpd : (2 : ℤ) ^ n ∣ p * (α - 1) := by
    rw [← hdx]
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [zpow_mul]
    exact hx1
  have hqd : (2 : ℤ) ^ n ∣ q * (α - 1) := by
    rw [← hdy]
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [zpow_mul]
    exact hy1
  obtain ⟨i, hi⟩ := exists_int_solve hn hα hpd
  obtain ⟨j, hj⟩ := exists_int_solve hn hα hqd
  have hxe : x ^ (p + i * (α + 1)) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [hdx, add_comm]; exact hi)
  have hye : y ^ (q + j * (α + 1)) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp (by rw [hdy, add_comm]; exact hj)
  have hmul : ∀ A B C D : ℤ, x ^ A * y ^ B * (x ^ C * y ^ D) = x ^ (A + C) * y ^ (B + D) := by
    intro A B C D
    have hc' : y ^ B * x ^ C = x ^ C * y ^ B := (hcxy.symm.zpow_zpow B C).eq
    calc x ^ A * y ^ B * (x ^ C * y ^ D) = x ^ A * (y ^ B * x ^ C) * y ^ D := by group
      _ = x ^ A * (x ^ C * y ^ B) * y ^ D := by rw [hc']
      _ = x ^ (A + C) * y ^ (B + D) := by simp only [zpow_add, mul_assoc]
  have hwα : (x ^ i * y ^ j) ^ α = x ^ (i * α) * y ^ (j * α) := by
    rw [(hcxy.zpow_zpow i j).mul_zpow, zpow_mul, zpow_mul]
  have hwW : x ^ i * y ^ j ∈ W := W.mul_mem (W.zpow_mem hxW i) (W.zpow_mem hyW j)
  refine ⟨x ^ i * y ^ j, hwW, ?_⟩
  have e1 : a * (x ^ i * y ^ j) * (a * (x ^ i * y ^ j)) =
      (a * (x ^ i * y ^ j) * a⁻¹) * (a * a) * (x ^ i * y ^ j) := by group
  rw [e1, haW _ hwW, hmuv, hwα,
    mul_assoc (x ^ (i * α) * y ^ (j * α)) (x ^ p * y ^ q) (x ^ i * y ^ j), hmul p q i j,
    hmul (i * α) (j * α) (p + i) (q + j)]
  have e2 : i * α + (p + i) = p + i * (α + 1) := by ring
  have e3 : j * α + (q + j) = q + j * (α + 1) := by ring
  rw [e2, e3, hxe, hye, one_mul]

end Action

end CFSG.CGT.PushingUpLit.SolKNA.R4
