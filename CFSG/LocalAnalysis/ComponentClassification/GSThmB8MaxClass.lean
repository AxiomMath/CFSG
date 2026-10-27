module

public import Mathlib.RingTheory.Int.Basic
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Eight.MC

open Subgroup

variable {G : Type*} [Group G]

structure Pres (P : Subgroup G) (p b : G) (β : ℤ) : Prop where
  p_mem : p ∈ P
  b_mem : b ∈ P
  b_not : b ∉ zpowers p
  b_sq : b * b = 1
  card : 2 * orderOf p = Nat.card P
  four_le : 4 ≤ orderOf p
  two_pow : ∃ k : ℕ, orderOf p = 2 ^ k
  rel : b * p * b⁻¹ = p ^ β
  beta : β = -1 ∨ β = (orderOf p : ℤ) / 2 - 1
  noncomm : b * p ≠ p * b

theorem dvd_of_dvd_mul_odd' {e : ℕ} {x y : ℤ} (hy : Odd y) (h : (2 ^ e : ℤ) ∣ x * y) :
    (2 ^ e : ℤ) ∣ x :=
  ((Int.isCoprime_two_left.mpr hy).pow_left).dvd_of_dvd_mul_right h

namespace Pres

variable {P : Subgroup G} {p b : G} {β : ℤ} (hP : Pres P p b β)
include hP

theorem orderOf_pos : 0 < orderOf p := lt_of_lt_of_le (by norm_num) hP.four_le

theorem four_dvd : 4 ∣ orderOf p := by
  obtain ⟨k, hk⟩ := hP.two_pow
  have h4 := hP.four_le
  rw [hk] at h4 ⊢
  rcases Nat.lt_or_ge k 2 with hlt | hk2
  · interval_cases k <;> norm_num at h4
  · exact ⟨2 ^ (k - 2), by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩

theorem eight_dvd_of_sd (hβ : β = (orderOf p : ℤ) / 2 - 1) : 8 ∣ orderOf p := by
  obtain ⟨k, hk⟩ := hP.two_pow
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · exfalso
    apply hP.noncomm
    have h4 := hP.four_le
    rw [hk] at h4
    have hk2 : k = 2 := by
      interval_cases k
      · norm_num at h4
      · norm_num at h4
      · rfl
    have hn4 : orderOf p = 4 := by rw [hk, hk2]; norm_num
    have h1 : b * p * b⁻¹ = p := by
      rw [hP.rel, hβ, hn4]
      norm_num
    calc b * p = b * p * b⁻¹ * b := by group
      _ = p * b := by rw [h1]
  · exact ⟨2 ^ (k - 3), by rw [hk, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩

omit hP in
theorem zpow_eq_zpow_iff (i j : ℤ) : p ^ i = p ^ j ↔ (orderOf p : ℤ) ∣ i - j := by
  rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, mul_inv_eq_one]

theorem conj_zpow (i : ℤ) : b * p ^ i * b⁻¹ = p ^ (β * i) := by
  have h1 : (MulAut.conj b) (p ^ i) = ((MulAut.conj b) p) ^ i := map_zpow _ p i
  simp only [MulAut.conj_apply] at h1
  rw [h1, hP.rel, ← zpow_mul]

theorem b_mul_zpow (i : ℤ) : b * p ^ i = p ^ (β * i) * b := by
  rw [← hP.conj_zpow i]
  group

theorem index_eq_two : ((zpowers p).subgroupOf P).index = 2 := by
  have hle : zpowers p ≤ P := zpowers_le.mpr hP.p_mem
  have h1 := Subgroup.card_mul_index ((zpowers p).subgroupOf P)
  rw [show Nat.card ((zpowers p).subgroupOf P) = orderOf p by
    rw [← Nat.card_zpowers]
    exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h1
  have h2 := hP.card
  have hpos := hP.orderOf_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])

theorem mem_cases {w : G} (hw : w ∈ P) : ∃ i : ℤ, w = p ^ i ∨ w = p ^ i * b := by
  by_cases hwp : w ∈ zpowers p
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hwp
    exact ⟨i, Or.inl rfl⟩
  · have h1 := (mul_mem_iff_of_index_two hP.index_eq_two (a := ⟨w, hw⟩)
      (b := ⟨b⁻¹, inv_mem hP.b_mem⟩)).mpr
    have h2 : (⟨w * b⁻¹, mul_mem hw (inv_mem hP.b_mem)⟩ : ↥P) ∈ (zpowers p).subgroupOf P := by
      refine h1 ⟨fun h3 => absurd (mem_subgroupOf.mp h3) hwp, fun h3 => ?_⟩
      exfalso
      have h4 : b⁻¹ ∈ zpowers p := mem_subgroupOf.mp h3
      exact hP.b_not (by simpa using inv_mem h4)
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (mem_subgroupOf.mp h2)
    refine ⟨i, Or.inr ?_⟩
    rw [hi]
    group

theorem exists_m : ∃ m : ℕ, orderOf p = 4 * m ∧ 1 ≤ m := by
  obtain ⟨m, hm⟩ := hP.four_dvd
  refine ⟨m, hm, ?_⟩
  have := hP.four_le
  omega

theorem a_mul_a : p ^ (orderOf p / 2) * p ^ (orderOf p / 2) = 1 := by
  obtain ⟨m, hm, -⟩ := hP.exists_m
  rw [← pow_add, show orderOf p / 2 + orderOf p / 2 = orderOf p by omega, pow_orderOf_eq_one]

theorem a_ne_one : p ^ (orderOf p / 2) ≠ 1 := by
  intro h1
  have h2 := orderOf_le_of_pow_eq_one (by obtain ⟨m, hm, hm1⟩ := hP.exists_m; omega) h1
  obtain ⟨m, hm, hm1⟩ := hP.exists_m
  omega

omit hP in
theorem a_eq_zpow : p ^ (orderOf p / 2) = p ^ ((orderOf p : ℤ) / 2) := by
  rw [← zpow_natCast]
  congr 1

theorem eq_one_or_a {y : G} (hy : y ∈ zpowers p) (h2 : y * y = 1) :
    y = 1 ∨ y = p ^ (orderOf p / 2) := by
  obtain ⟨m, hm, hm1⟩ := hP.exists_m
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_add, ← two_mul, ← orderOf_dvd_iff_zpow_eq_one, hm] at h2
  push_cast at h2
  have h3 : (2 * m : ℤ) ∣ i := by
    have : (2 : ℤ) * (2 * m) ∣ 2 * i := by rw [← mul_assoc]; exact h2
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp this
  obtain ⟨t, rfl⟩ := h3
  have ha : p ^ (orderOf p / 2) = p ^ ((2 * m : ℕ) : ℤ) := by
    rw [zpow_natCast]
    congr 1
    omega
  rcases Int.even_or_odd t with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · left
    rw [show (2 * (m : ℤ)) * (s + s) = (orderOf p : ℤ) * s by rw [hm]; push_cast; ring,
      zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · right
    rw [ha, show (2 * (m : ℤ)) * (2 * s + 1) = (orderOf p : ℤ) * s + ((2 * m : ℕ) : ℤ) by
      rw [hm]; push_cast; ring, zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow,
      one_mul]

theorem conj_a : b * p ^ (orderOf p / 2) * b⁻¹ = p ^ (orderOf p / 2) := by
  have hmem : b * p ^ (orderOf p / 2) * b⁻¹ ∈ zpowers p := by
    rw [a_eq_zpow (p := p), hP.conj_zpow]
    exact zpow_mem (mem_zpowers p) _
  have h2 : b * p ^ (orderOf p / 2) * b⁻¹ * (b * p ^ (orderOf p / 2) * b⁻¹) = 1 := by
    rw [show b * p ^ (orderOf p / 2) * b⁻¹ * (b * p ^ (orderOf p / 2) * b⁻¹) =
      b * (p ^ (orderOf p / 2) * p ^ (orderOf p / 2)) * b⁻¹ by group, hP.a_mul_a]
    group
  rcases hP.eq_one_or_a hmem h2 with h1 | h1
  · exfalso
    apply hP.a_ne_one
    calc p ^ (orderOf p / 2) = b⁻¹ * (b * p ^ (orderOf p / 2) * b⁻¹) * b := by group
      _ = 1 := by rw [h1]; group
  · exact h1

theorem sq_zpow_mul_b (i : ℤ) : p ^ i * b * (p ^ i * b) = p ^ ((1 + β) * i) := by
  rw [show p ^ i * b * (p ^ i * b) = p ^ i * (b * p ^ i * b⁻¹) * (b * b) by
    group, hP.conj_zpow, hP.b_sq, mul_one, ← zpow_add]
  congr 1
  ring

theorem comm_b_iff {y : G} (hy : y ∈ zpowers p) :
    b * y = y * b ↔ y = 1 ∨ y = p ^ (orderOf p / 2) := by
  constructor
  · intro hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    have h1 : p ^ (β * i) = p ^ i := by
      rw [← hP.conj_zpow, hc]
      group
    rw [zpow_eq_zpow_iff] at h1
    obtain ⟨m, hm, hm1⟩ := hP.exists_m
    refine hP.eq_one_or_a (zpow_mem (mem_zpowers p) i) ?_
    rw [← zpow_add, ← two_mul, ← orderOf_dvd_iff_zpow_eq_one, hm]
    push_cast
    rw [hm] at h1
    push_cast at h1
    rcases hP.beta with hβ | hβ
    · rw [hβ] at h1
      have : (4 * (m : ℤ)) ∣ -(2 * i) := by
        convert h1 using 1
        ring
      exact (dvd_neg).mp this
    · have h8 := hP.eight_dvd_of_sd hβ
      rw [hm] at hβ h8
      push_cast at hβ
      have hβ' : β = 2 * m - 1 := by rw [hβ]; omega
      rw [hβ'] at h1
      have h2 : (2 * (2 * (m : ℤ))) ∣ 2 * ((m - 1) * i) := by
        convert h1 using 1 <;> ring
      have h3 : (2 * (m : ℤ)) ∣ (m - 1) * i :=
        (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
      have hmodd : Odd ((m : ℤ) - 1) := by
        obtain ⟨t, ht⟩ := h8
        exact ⟨(t : ℤ) - 1, by omega⟩
      obtain ⟨k, hk⟩ := hP.two_pow
      have h2m : (2 * (m : ℤ)) = 2 ^ (k - 1) := by
        have hk' : (4 * m : ℕ) = 2 ^ k := hm ▸ hk
        rcases Nat.lt_or_ge k 1 with hk0 | hk1
        · interval_cases k
          omega
        · have : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          have h5 : 2 * m = 2 ^ (k - 1) := by omega
          exact_mod_cast h5
      have hcop : IsCoprime (2 * (m : ℤ)) ((m : ℤ) - 1) := by
        rw [h2m]
        exact (Int.isCoprime_two_left.mpr hmodd).pow_left
      have h4 := hcop.dvd_of_dvd_mul_left h3
      obtain ⟨t, ht⟩ := h4
      exact ⟨t, by rw [ht]; ring⟩
  · rintro (rfl | rfl)
    · group
    · calc b * p ^ (orderOf p / 2) = b * p ^ (orderOf p / 2) * b⁻¹ * b := by group
        _ = p ^ (orderOf p / 2) * b := by rw [hP.conj_a]

theorem zpow_mul_b_not_mem (i : ℤ) : p ^ i * b ∉ zpowers p := by
  intro h1
  apply hP.b_not
  have := mul_mem (inv_mem (zpow_mem (mem_zpowers p) i)) h1
  rwa [inv_mul_cancel_left] at this

theorem mem_of_comm (j : ℤ) {w : G} (hw : w ∈ P) (hc : w * (p ^ j * b) = p ^ j * b * w) :
    w = 1 ∨ w = p ^ (orderOf p / 2) ∨ w = p ^ j * b ∨ w = p ^ (orderOf p / 2) * (p ^ j * b) := by
  obtain ⟨i, rfl | rfl⟩ := hP.mem_cases hw
  ·
    have h1 : b * p ^ i = p ^ i * b := by
      have h2 : p ^ j * (p ^ i * b) = p ^ j * (b * p ^ i) := by
        calc p ^ j * (p ^ i * b) = p ^ i * (p ^ j * b) := by
              rw [← mul_assoc, ← mul_assoc, ← zpow_add, ← zpow_add, add_comm]
          _ = p ^ j * b * p ^ i := hc
          _ = p ^ j * (b * p ^ i) := by group
      exact (mul_left_cancel h2).symm
    rcases (hP.comm_b_iff (zpow_mem (mem_zpowers p) i)).mp h1 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
  ·
    have h1 : b * p ^ (i - j) = p ^ (i - j) * b := by
      have e1 : p ^ i * b * (p ^ j * b) = p ^ i * p ^ (β * j) := by
        rw [show p ^ i * b * (p ^ j * b) = p ^ i * (b * p ^ j * b⁻¹) * (b * b) by group,
          hP.conj_zpow, hP.b_sq, mul_one]
      have e2 : p ^ j * b * (p ^ i * b) = p ^ j * p ^ (β * i) := by
        rw [show p ^ j * b * (p ^ i * b) = p ^ j * (b * p ^ i * b⁻¹) * (b * b) by group,
          hP.conj_zpow, hP.b_sq, mul_one]
      have e3 : p ^ i * p ^ (β * j) = p ^ j * p ^ (β * i) := by rw [← e1, ← e2, hc]
      rw [← zpow_add, ← zpow_add] at e3
      rw [hP.b_mul_zpow, mul_left_inj, zpow_eq_zpow_iff]
      rw [zpow_eq_zpow_iff] at e3
      rw [show β * (i - j) - (i - j) = -(i + β * j - (j + β * i)) by ring]
      exact dvd_neg.mpr e3
    have hw' : p ^ i * b = p ^ (i - j) * (p ^ j * b) := by
      rw [← mul_assoc, ← zpow_add]
      congr 2
      ring
    rcases (hP.comm_b_iff (zpow_mem (mem_zpowers p) (i - j))).mp h1 with h3 | h3
    · right; right; left
      rw [hw', h3, one_mul]
    · right; right; right
      rw [hw', h3]

theorem card_le_four [Finite G] {E : Subgroup G} (hEP : E ≤ P) (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 4 := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have h1 := hE _ (mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE y hy)
    calc x * y = (y⁻¹ * x⁻¹) := by rw [← mul_inv_rev]; exact (inv_eq_of_mul_eq_one_right h1).symm
      _ = y * x := by rw [hx', hy']
  set a := p ^ (orderOf p / 2) with ha
  have hcard_a : Nat.card (zpowers a) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hP.a_mul_a)
  by_cases hEp : E ≤ zpowers p
  · have hle : E ≤ zpowers a := by
      intro e he
      rcases hP.eq_one_or_a (hEp he) (hE e he) with h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact mem_zpowers _
    exact (card_le_of_le hle).trans (hcard_a.trans (by norm_num))
  · obtain ⟨u, huE, hup⟩ := Set.not_subset.mp hEp
    obtain ⟨j, rfl | rfl⟩ := hP.mem_cases (hEP huE)
    · exact absurd (zpow_mem (mem_zpowers p) j) hup
    · have hle : E ≤ zpowers a ⊔ zpowers (p ^ j * b) := by
        intro e he
        rcases hP.mem_of_comm j (hEP he) (hcomm e he _ huE) with h1 | h1 | h1 | h1
        · rw [h1]; exact one_mem _
        · rw [h1]; exact mem_sup_left (mem_zpowers _)
        · rw [h1]; exact mem_sup_right (mem_zpowers _)
        · rw [h1]; exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
      have hcomm' : ∀ x ∈ zpowers a, ∀ y ∈ zpowers (p ^ j * b), x * y = y * x := by
        intro x hx y hy
        obtain ⟨s, rfl⟩ := mem_zpowers_iff.mp hx
        obtain ⟨t, rfl⟩ := mem_zpowers_iff.mp hy
        have hab : a * (p ^ j * b) = p ^ j * b * a := by
          have h1 : a * p ^ j = p ^ j * a := by
            rw [ha, ← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]
          have h2 : a * b = b * a := by
            have h3 : b * a * b⁻¹ = a := hP.conj_a
            calc a * b = (b * a * b⁻¹) * b := by rw [h3]
              _ = b * a := by group
          calc a * (p ^ j * b) = (a * p ^ j) * b := by group
            _ = p ^ j * (a * b) := by rw [h1]; group
            _ = p ^ j * b * a := by rw [h2]; group
        exact (Commute.zpow_zpow hab s t).eq
      have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers a)
        (zpowers (p ^ j * b)) hcomm').1
      have hcard_u : Nat.card (zpowers (p ^ j * b)) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hE _ huE)
      have h2 : Nat.card ↥(zpowers a ⊔ zpowers (p ^ j * b)) ≤ 4 := by
        have h3 : Nat.card ↥(zpowers a ⊔ zpowers (p ^ j * b)) ≤
            Nat.card ↥(zpowers a ⊔ zpowers (p ^ j * b)) *
              Nat.card ↥(zpowers a ⊓ zpowers (p ^ j * b)) :=
          Nat.le_mul_of_pos_right _ Nat.card_pos
        rw [h1] at h3
        nlinarith
      exact (card_le_of_le hle).trans h2

theorem a_zpow_eq_one_iff (k : ℤ) : (p ^ (orderOf p / 2)) ^ k = 1 ↔ Even k := by
  obtain ⟨m, hm, hm1⟩ := hP.exists_m
  rw [a_eq_zpow (p := p), ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hm]
  push_cast
  rw [show (4 * (m : ℤ)) / 2 = 2 * m by omega]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by
      have h2 : (2 * (m : ℤ)) * k = (2 * m) * (t + t) := by rw [ht]; ring
      exact mul_left_cancel₀ (by omega) h2⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by ring⟩

theorem a_zpow_odd {k : ℤ} (hk : Odd k) : (p ^ (orderOf p / 2)) ^ k = p ^ (orderOf p / 2) := by
  obtain ⟨t, rfl⟩ := hk
  rw [zpow_add, zpow_one, zpow_mul, (hP.a_zpow_eq_one_iff 2).mpr even_two, one_zpow, one_mul]

theorem even_of_zpow_two_mul_eq_a (h8 : 8 ∣ orderOf p) {k : ℤ}
    (hk : p ^ (2 * k) = p ^ (orderOf p / 2)) : Even k := by
  obtain ⟨m, hm, hm1⟩ := hP.exists_m
  rw [a_eq_zpow (p := p), zpow_eq_zpow_iff, hm] at hk
  push_cast at hk
  rw [show (4 * (m : ℤ)) / 2 = 2 * m by omega] at hk
  rw [hm] at h8
  obtain ⟨t, ht⟩ := h8
  obtain ⟨c, hc⟩ := hk
  have hm' : (m : ℤ) = 2 * t := by omega
  rw [hm'] at hc
  have : k = 2 * t + 4 * (t * c) := by linarith
  exact ⟨t + 2 * (t * c), by rw [this]; ring⟩

omit hP in
theorem a_comm_zpow (i : ℤ) : p ^ (orderOf p / 2) * p ^ i = p ^ i * p ^ (orderOf p / 2) := by
  rw [← zpow_natCast, ← zpow_add, ← zpow_add, add_comm]

theorem a_comm_b : p ^ (orderOf p / 2) * b = b * p ^ (orderOf p / 2) := by
  calc p ^ (orderOf p / 2) * b = (b * p ^ (orderOf p / 2) * b⁻¹) * b := by rw [hP.conj_a]
    _ = b * p ^ (orderOf p / 2) := by group

omit hP in
theorem sigma_zpow {σ : G} (hσp : σ * p * σ⁻¹ = p ^ (orderOf p / 2) * p) (i : ℤ) :
    σ * p ^ i * σ⁻¹ = (p ^ (orderOf p / 2)) ^ i * p ^ i := by
  have h1 : (MulAut.conj σ) (p ^ i) = ((MulAut.conj σ) p) ^ i := map_zpow _ p i
  simp only [MulAut.conj_apply] at h1
  rw [h1, hσp]
  exact (Commute.mul_zpow (show Commute (p ^ (orderOf p / 2)) p from by
    rw [Commute, SemiconjBy, ← pow_succ, ← pow_succ']) i)

theorem e8_lemma (h8 : 8 ∣ orderOf p) {σ : G} (hσ2 : σ * σ = 1) (hσb : σ * b = b * σ)
    (hσp : σ * p * σ⁻¹ = p ^ (orderOf p / 2) * p) {π u : G} (hπ : π ∈ P) (hu : u ∈ P)
    (hup : u ∉ zpowers p) (hu2 : u * u = 1) (h1 : σ * π * (σ * π) = 1)
    (h2 : σ * π * u = u * (σ * π)) :
    (∃ i : ℤ, π = p ^ (2 * i) ∨ π = p ^ (2 * i) * b) ∧ ∃ j : ℤ, u = p ^ (2 * j) * b := by
  set A := p ^ (orderOf p / 2) with hA
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσbσ : σ * b * σ⁻¹ = b := by rw [hσb]; group
  have hψb : ∀ i : ℤ, σ * (p ^ i * b) * σ⁻¹ = A ^ i * p ^ i * b := fun i => by
    rw [show σ * (p ^ i * b) * σ⁻¹ = (σ * p ^ i * σ⁻¹) * (σ * b * σ⁻¹) by group,
      sigma_zpow hσp, hσbσ]
  have h1' : σ * π * σ⁻¹ * π = 1 := by rw [hσinv, mul_assoc (σ * π) σ π]; exact h1
  have h2' : σ * (π * u * π⁻¹) * σ⁻¹ = u := by
    calc σ * (π * u * π⁻¹) * σ⁻¹ = (σ * π * u) * (σ * π)⁻¹ := by group
      _ = u := by rw [h2]; group
  obtain ⟨j, hj | rfl⟩ := hP.mem_cases hu
  · exact absurd (hj ▸ zpow_mem (mem_zpowers p) j) hup
  obtain ⟨i, rfl | rfl⟩ := hP.mem_cases hπ
  ·
    rw [sigma_zpow hσp, mul_assoc, ← zpow_add, ← two_mul] at h1'
    have hi : Even i := by
      by_contra hio
      rw [Int.not_even_iff_odd] at hio
      rw [hP.a_zpow_odd hio] at h1'
      have h3 : p ^ (2 * i) = A := by
        calc p ^ (2 * i) = A⁻¹ * (A * p ^ (2 * i)) := by group
          _ = A := by rw [h1', mul_one]; exact inv_eq_of_mul_eq_one_right hP.a_mul_a
      exact (Int.not_even_iff_odd.mpr hio) (hP.even_of_zpow_two_mul_eq_a h8 h3)
    have hπ2 : p ^ i * p ^ i = 1 := by
      rw [(hP.a_zpow_eq_one_iff i).mpr hi, one_mul] at h1'
      rw [← zpow_add, ← two_mul]
      exact h1'
    have hπa := hP.eq_one_or_a (zpow_mem (mem_zpowers p) i) hπ2
    have hconj : p ^ i * (p ^ j * b) * (p ^ i)⁻¹ = p ^ j * b := by
      rcases hπa with h3 | h3
      · rw [h3]; group
      · rw [h3]
        have hc1 := a_comm_zpow (p := p) j
        have hc2 := hP.a_comm_b
        calc p ^ (orderOf p / 2) * (p ^ j * b) * (p ^ (orderOf p / 2))⁻¹
            = (p ^ (orderOf p / 2) * p ^ j) * b * (p ^ (orderOf p / 2))⁻¹ := by group
          _ = p ^ j * (p ^ (orderOf p / 2) * b) * (p ^ (orderOf p / 2))⁻¹ := by
              rw [hc1]; group
          _ = p ^ j * b := by rw [hc2]; group
    rw [hconj, hψb] at h2'
    have hAj : A ^ j = 1 := by
      have := mul_right_cancel h2'
      calc A ^ j = A ^ j * p ^ j * (p ^ j)⁻¹ := by group
        _ = 1 := by rw [this]; group
    obtain ⟨j', hj'⟩ := (hP.a_zpow_eq_one_iff j).mp hAj
    refine ⟨?_, ⟨j', by rw [hj', ← two_mul]⟩⟩
    rcases hπa with h3 | h3
    · exact ⟨0, Or.inl (by rw [h3]; simp)⟩
    · refine ⟨(orderOf p / 2 / 2 : ℕ), Or.inl ?_⟩
      rw [h3, ← zpow_natCast]
      congr 1
      obtain ⟨m, hm, -⟩ := hP.exists_m
      rw [hm]
      push_cast
      omega
  ·
    have e1 : σ * (p ^ i * b) * σ⁻¹ * (p ^ i * b) = A ^ i * p ^ ((1 + β) * i) := by
      rw [hψb, ← hP.sq_zpow_mul_b i]
      group
    rw [e1] at h1'
    have e2 : p ^ i * b * (p ^ j * b) * (p ^ i * b)⁻¹ = p ^ (i + β * (j - i)) * b := by
      rw [show p ^ i * b * (p ^ j * b) * (p ^ i * b)⁻¹ =
          p ^ i * (b * p ^ (j - i) * b⁻¹) * b by
        rw [zpow_sub]; group, hP.conj_zpow, ← zpow_add]
    rw [e2, hψb] at h2'
    have h3 : A ^ (i + β * (j - i)) * p ^ (i + β * (j - i) - j) = 1 := by
      have := mul_right_cancel h2'
      rw [zpow_sub, ← mul_assoc, this]
      group
    rcases hP.beta with hβ | hβ
    ·
      rw [hβ] at h1' h3
      rw [show (1 + (-1 : ℤ)) * i = 0 by ring, zpow_zero, mul_one] at h1'
      have hi := (hP.a_zpow_eq_one_iff i).mp h1'
      have hj : Even j := by
        by_contra hjo
        rw [Int.not_even_iff_odd] at hjo
        have hpar : Odd (i + -1 * (j - i)) := by
          obtain ⟨t, ht⟩ := hi
          obtain ⟨s, hs⟩ := hjo
          exact ⟨2 * t - s - 1, by rw [ht, hs]; ring⟩
        rw [hP.a_zpow_odd hpar] at h3
        have h4 : p ^ (2 * (i - j)) = A := by
          have h5 : p ^ (i + -1 * (j - i) - j) = A⁻¹ := by
            calc p ^ (i + -1 * (j - i) - j) = A⁻¹ * (A * p ^ (i + -1 * (j - i) - j)) := by
                  group
              _ = A⁻¹ := by rw [h3, mul_one]
          rw [show 2 * (i - j) = i + -1 * (j - i) - j by ring, h5]
          exact inv_eq_of_mul_eq_one_right hP.a_mul_a
        have h6 := hP.even_of_zpow_two_mul_eq_a h8 h4
        obtain ⟨t, ht⟩ := hi
        obtain ⟨s, hs⟩ := hjo
        obtain ⟨r, hr⟩ := h6
        omega
      obtain ⟨t, ht⟩ := hi
      obtain ⟨s, hs⟩ := hj
      exact ⟨⟨t, Or.inr (by rw [ht, ← two_mul])⟩, ⟨s, by rw [hs, ← two_mul]⟩⟩
    ·
      obtain ⟨m, hm, hm1⟩ := hP.exists_m
      have hβ' : β = 2 * m - 1 := by rw [hβ, hm]; push_cast; omega
      have hj : Even j := by
        have hu2' := hu2
        rw [hP.sq_zpow_mul_b, hβ', show (1 + (2 * (m : ℤ) - 1)) * j = (2 * m : ℕ) * j by
          push_cast; ring, zpow_mul, zpow_natCast,
          show 2 * m = orderOf p / 2 by omega] at hu2'
        exact (hP.a_zpow_eq_one_iff j).mp hu2'
      have hi : Even i := by
        by_contra hio
        rw [Int.not_even_iff_odd] at hio
        have h5 : p ^ (i + β * (j - i) - j) = A ^ (-(i - j)) * p ^ (2 * (i - j)) := by
          rw [hA, ← zpow_natCast, ← zpow_mul, ← zpow_add, hβ']
          congr 1
          rw [show orderOf p / 2 = 2 * m by omega]
          push_cast
          ring
        rw [h5, ← mul_assoc, ← zpow_add] at h3
        have hpar : Odd (i + β * (j - i) + -(i - j)) := by
          obtain ⟨t, ht⟩ := hio
          obtain ⟨s, hs⟩ := hj
          rw [hβ']
          exact ⟨2 * (m : ℤ) * s - 2 * m * t - m + t, by rw [ht, hs]; ring⟩
        rw [hP.a_zpow_odd hpar] at h3
        have h4 : p ^ (2 * (i - j)) = A := by
          calc p ^ (2 * (i - j)) = A⁻¹ * (A * p ^ (2 * (i - j))) := by group
            _ = A := by rw [h3, mul_one]; exact inv_eq_of_mul_eq_one_right hP.a_mul_a
        have h6 := hP.even_of_zpow_two_mul_eq_a h8 h4
        obtain ⟨t, ht⟩ := hio
        obtain ⟨s, hs⟩ := hj
        obtain ⟨r, hr⟩ := h6
        omega
      obtain ⟨t, ht⟩ := hi
      obtain ⟨s, hs⟩ := hj
      exact ⟨⟨t, Or.inr (by rw [ht, ← two_mul])⟩, ⟨s, by rw [hs, ← two_mul]⟩⟩

theorem m_two_pow : ∃ m e : ℕ, orderOf p = 4 * m ∧ 1 ≤ m ∧ m = 2 ^ e := by
  obtain ⟨k, hk⟩ := hP.two_pow
  obtain ⟨m, hm, hm1⟩ := hP.exists_m
  refine ⟨m, k - 2, hm, hm1, ?_⟩
  have h4 := hP.four_le
  rw [hk] at h4 hm
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k <;> norm_num at h4
    · exact hge
  have : (2 : ℕ) ^ k = 4 * 2 ^ (k - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  omega

theorem zpow_four_of_conj_b {w : G} (hw : w ∈ P)
    (hwb : w * b * w⁻¹ = b ∨ w * b * w⁻¹ = p ^ (orderOf p / 2) * b) :
    ∃ i : ℤ, (w = p ^ i ∨ w = p ^ i * b) ∧ p ^ (4 * i) = 1 := by
  obtain ⟨m, hm, hm1⟩ := hP.exists_m
  have key : ∀ i : ℤ, p ^ ((1 - β) * i) = 1 ∨ p ^ ((1 - β) * i) = p ^ (orderOf p / 2) →
      p ^ (4 * i) = 1 := by
    intro i hi
    have h2 : p ^ (2 * ((1 - β) * i)) = 1 := by
      rcases hi with h | h
      · rw [mul_comm, zpow_mul, h, one_zpow]
      · rw [mul_comm, zpow_mul, h, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one,
          hm]
        push_cast
        exact ⟨1, by omega⟩
    rw [← orderOf_dvd_iff_zpow_eq_one] at h2 ⊢
    rcases hP.beta with hβ | hβ
    · rw [hβ] at h2
      convert h2 using 1
      ring
    · rw [hm] at hβ h2 ⊢
      push_cast at hβ h2 ⊢
      rw [show (4 * (m : ℤ)) / 2 = 2 * m by omega] at hβ
      rw [hβ] at h2
      have : 4 * i = 2 * ((1 - (2 * m - 1)) * i) + (4 * m) * i := by ring
      rw [this]
      exact dvd_add h2 (dvd_mul_right _ _)
  have hconj : ∀ i : ℤ, p ^ i * b * (p ^ i)⁻¹ = p ^ ((1 - β) * i) * b := fun i => by
    rw [show p ^ i * b * (p ^ i)⁻¹ = p ^ i * (b * p ^ (-i) * b⁻¹) * b by
      rw [zpow_neg]; group, hP.conj_zpow, ← zpow_add]
    congr 2
    ring
  obtain ⟨i, rfl | rfl⟩ := hP.mem_cases hw
  · refine ⟨i, Or.inl rfl, key i ?_⟩
    rw [hconj] at hwb
    rcases hwb with h | h
    · left
      exact mul_right_cancel (h.trans (one_mul b).symm)
    · right
      exact mul_right_cancel h
  · refine ⟨i, Or.inr rfl, key i ?_⟩
    have e1 : p ^ i * b * b * (p ^ i * b)⁻¹ = p ^ ((1 - β) * i) * b := by
      rw [show p ^ i * b * b * (p ^ i * b)⁻¹ = p ^ i * b * (p ^ i)⁻¹ by group, hconj]
    rw [e1] at hwb
    rcases hwb with h | h
    · left
      exact mul_right_cancel (h.trans (one_mul b).symm)
    · right
      exact mul_right_cancel h

theorem eq_or_eq_inv_of_sq_eq_a {y y' : G} (hy : y ∈ zpowers p) (hy' : y' ∈ zpowers p)
    (h1 : y * y = p ^ (orderOf p / 2)) (h2 : y' * y' = p ^ (orderOf p / 2)) :
    y' = y ∨ y' = y⁻¹ := by
  obtain ⟨s, rfl⟩ := mem_zpowers_iff.mp hy
  obtain ⟨t, rfl⟩ := mem_zpowers_iff.mp hy'
  have hc : p ^ (t - s) * p ^ (t - s) = 1 := by
    have e1 : p ^ (t - s) * p ^ (t - s) = (p ^ t * p ^ t) * (p ^ s * p ^ s)⁻¹ := by
      rw [← zpow_add, ← zpow_add, ← zpow_add, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [e1, h1, h2, mul_inv_cancel]
  rcases hP.eq_one_or_a (zpow_mem (mem_zpowers p) (t - s)) hc with h3 | h3
  · left
    calc p ^ t = p ^ (t - s) * p ^ s := by rw [← zpow_add]; ring_nf
      _ = p ^ s := by rw [h3, one_mul]
  · right
    have h4 : p ^ s * p ^ s * (p ^ s * p ^ s) = 1 := by rw [h1, hP.a_mul_a]
    calc p ^ t = p ^ (t - s) * p ^ s := by rw [← zpow_add]; ring_nf
      _ = p ^ s * p ^ s * p ^ s := by rw [h3, ← h1]
      _ = (p ^ s)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc p ^ s * p ^ s * p ^ s * p ^ s = p ^ s * p ^ s * (p ^ s * p ^ s) := by group
          _ = 1 := h4

theorem conj_eq_or_of_comm {σ : G} (hσ2 : σ * σ = 1) {k : ℤ} (hk : σ * p * σ⁻¹ = p ^ k)
    {i : ℤ} (hi4 : p ^ (4 * i) = 1) (hi2 : p ^ (2 * i) ≠ 1) (hσy : σ * p ^ i = p ^ i * σ) :
    σ * p * σ⁻¹ = p ∨ σ * p * σ⁻¹ = p ^ (orderOf p / 2) * p := by
  obtain ⟨m, e, hm, hm1, hme⟩ := hP.m_two_pow
  have hconj : ∀ j : ℤ, σ * p ^ j * σ⁻¹ = p ^ (k * j) := fun j => by
    have h1 : (MulAut.conj σ) (p ^ j) = ((MulAut.conj σ) p) ^ j := map_zpow _ p j
    simp only [MulAut.conj_apply] at h1
    rw [h1, hk, ← zpow_mul]
  have h1 : (orderOf p : ℤ) ∣ (k - 1) * i := by
    rw [orderOf_dvd_iff_zpow_eq_one, sub_mul, one_mul, zpow_sub, ← hconj, hσy]
    group
  rw [← orderOf_dvd_iff_zpow_eq_one, hm] at hi4
  push_cast at hi4
  have hmi : (m : ℤ) ∣ i := (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hi4
  obtain ⟨u, rfl⟩ := hmi
  have hu : Odd u := by
    rw [← Int.not_even_iff_odd]
    rintro ⟨v, rfl⟩
    apply hi2
    rw [← orderOf_dvd_iff_zpow_eq_one, hm]
    push_cast
    exact ⟨v, by ring⟩
  rw [hm] at h1
  push_cast at h1
  have h2 : (4 : ℤ) ∣ (k - 1) * u := by
    have : (m : ℤ) * 4 ∣ (m : ℤ) * ((k - 1) * u) := by
      convert h1 using 1 <;> ring
    exact (mul_dvd_mul_iff_left (by omega : (m : ℤ) ≠ 0)).mp this
  have h3 : (2 ^ 2 : ℤ) ∣ k - 1 := dvd_of_dvd_mul_odd' hu (by norm_num; exact h2)
  obtain ⟨c, hc⟩ := h3
  have h4 : (orderOf p : ℤ) ∣ k * k - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, zpow_one, mul_inv_eq_one, ← hconj]
    calc σ * p ^ k * σ⁻¹ = σ * (σ * p * σ⁻¹) * σ⁻¹ := by rw [hk]
      _ = (σ * σ) * p * (σ * σ)⁻¹ := by group
      _ = p := by rw [hσ2]; group
  have hk' : k = 4 * c + 1 := by
    have := hc
    linarith
  rw [hm, hk'] at h4
  push_cast at h4
  replace h4 : (4 : ℤ) * m ∣ 4 * (2 * c * (2 * c + 1)) := by
    convert h4 using 1
    ring
  have h5 : (m : ℤ) ∣ 2 * c * (2 * c + 1) :=
    (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4
  have h6 : (m : ℤ) ∣ 2 * c := by
    rw [hme] at h5 ⊢
    push_cast at h5 ⊢
    exact dvd_of_dvd_mul_odd' ⟨c, rfl⟩ h5
  obtain ⟨r, hr⟩ := h6
  have h7 : p ^ (k - 1) = (p ^ (orderOf p / 2)) ^ r := by
    rw [a_eq_zpow (p := p), ← zpow_mul, hc, hm]
    push_cast
    rw [show (4 * (m : ℤ)) / 2 = 2 * m by omega]
    congr 1
    have : (4 : ℤ) * c = 2 * (m * r) := by rw [← hr]; ring
    rw [this]
    ring
  rw [hk, show k = (k - 1) + 1 by ring, zpow_add, zpow_one, h7]
  rcases Int.even_or_odd r with hr' | hr'
  · left
    rw [(hP.a_zpow_eq_one_iff r).mpr hr', one_mul]
  · right
    rw [hP.a_zpow_odd hr']

theorem eight_dvd_of_ne_four (h4 : orderOf p ≠ 4) : 8 ∣ orderOf p := by
  obtain ⟨m, e, hm, hm1, hme⟩ := hP.m_two_pow
  rcases Nat.eq_zero_or_pos e with he | he
  · rw [he, pow_zero] at hme
    omega
  · refine ⟨2 ^ (e - 1), ?_⟩
    have : 2 ^ e = 2 * 2 ^ (e - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hm, hme]
    omega

theorem zpow_two_eq (hbp : p * b * p⁻¹ * b⁻¹ = p ^ (1 - β)) :
    p ^ (2 : ℤ) = p * b * p⁻¹ * b⁻¹ ∨ p ^ (2 : ℤ) = p * b * p⁻¹ * b⁻¹ * p ^ (orderOf p / 2) := by
  obtain ⟨m, hm, hm1⟩ := hP.exists_m
  rw [hbp]
  rcases hP.beta with hβ | hβ
  · left
    rw [hβ]
    norm_num
  · right
    rw [hβ, a_eq_zpow (p := p), ← zpow_add, hm]
    push_cast
    congr 1
    omega

end Pres

end Eight.MC

end CFSG.ComponentClassification.GSThmB
