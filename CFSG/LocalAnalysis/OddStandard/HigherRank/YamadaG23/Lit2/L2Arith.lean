module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.Blueprint.Multiplier

private lemma four_dvd_lcm {u v : ℕ} (h : 4 ∣ u.lcm v) : 4 ∣ u ∨ 4 ∣ v := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hu, hv⟩ := hc
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero 4)
  have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ dvd_zero 4)
  have h4 : 2 ^ 2 ∣ u.lcm v := by simpa using h
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.lcm_ne_zero hu0 hv0)] at h4
  have hu2 : u.factorization 2 ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    exact hu (by
      show 2 ^ 2 ∣ u
      rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hu0]
      omega)
  have hv2 : v.factorization 2 ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    exact hv (by
      show 2 ^ 2 ∣ v
      rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hv0]
      omega)
  have hlcm := Nat.factorization_lcm hu0 hv0
  have hval : (u.lcm v).factorization 2 = max (u.factorization 2) (v.factorization 2) := by
    rw [hlcm, Finsupp.sup_apply]
  omega

private lemma four_dvd_of_zmod {a : ℕ} (x : Multiplicative (ZMod a)) (h : 4 ∣ orderOf x) :
    4 ∣ a := by
  have h1 : orderOf x ∣ Nat.card (Multiplicative (ZMod a)) := orderOf_dvd_natCard x
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod] at h1
  exact h.trans h1

private lemma odd_sq_modEq_one (q : ℕ) (hq : Odd q) : q ^ 2 ≡ 1 [MOD 4] := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
  rw [h]
  exact Nat.ModEq.modulus_mul_add

private lemma odd_pow_modEq_self (q n : ℕ) (hq : Odd q) (hn : Odd n) : q ^ n ≡ q [MOD 4] := by
  obtain ⟨k, rfl⟩ := hn
  have hpow : q ^ (2 * k + 1) = q * (q ^ 2) ^ k := by
    rw [pow_succ, pow_mul, mul_comm]
  rw [hpow]
  calc q * (q ^ 2) ^ k ≡ q * 1 ^ k [MOD 4] :=
        Nat.ModEq.mul_left q ((odd_sq_modEq_one q hq).pow k)
    _ = q := by simp

private lemma four_dvd_sub_one_of_odd_pow {q n : ℕ} (hq : Odd q) (hn : Odd n)
    (h : 4 ∣ q ^ n - 1) : 4 ∣ q - 1 := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Odd.pos hq).ne'
  have hqn1 : 1 ≤ q ^ n := one_le_pow₀ hq1
  have h1 : q ^ n ≡ 1 [MOD 4] := by
    rw [Nat.ModEq.comm]
    exact (Nat.modEq_iff_dvd' hqn1).mpr h
  have h2 : q ^ n ≡ q [MOD 4] := odd_pow_modEq_self q n hq hn
  have h3 : 1 ≡ q [MOD 4] := h1.symm.trans h2
  exact (Nat.modEq_iff_dvd' hq1).mp h3

private lemma odd_of_four_dvd_pow_add_one {q n : ℕ} (hn : n ≠ 0) (h : 4 ∣ q ^ n + 1) :
    Odd q := by
  by_contra hq
  rw [Nat.not_odd_iff_even] at hq
  obtain ⟨k, rfl⟩ := hq
  have he : Even ((k + k) ^ n) := (even_iff_two_dvd.mpr ⟨k, by ring⟩).pow_of_ne_zero hn
  have hodd : Odd ((k + k) ^ n + 1) := he.add_one
  have h2 : Even ((k + k) ^ n + 1) := even_iff_two_dvd.mpr (dvd_trans (by norm_num) h)
  exact Nat.not_odd_iff_even.mpr h2 hodd

private lemma not_four_dvd_pow_add_one_of_even (q : ℕ) (hq : Odd q) {n : ℕ} (hn : Even n) :
    ¬ 4 ∣ q ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  intro h
  have h0 : q ^ (k + k) + 1 ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h
  have h1 : q ^ (k + k) + 1 ≡ 2 [MOD 4] := by
    have hp : q ^ (k + k) ≡ 1 [MOD 4] := by
      rw [show k + k = 2 * k from by ring, pow_mul]
      simpa using (odd_sq_modEq_one q hq).pow k
    simpa using hp.add (Nat.ModEq.refl 1)
  have h20 : (2 : ℕ) ≡ 0 [MOD 4] := h1.symm.trans h0
  exact (by have hd : 4 ∣ 2 := Nat.modEq_zero_iff_dvd.mp h20; omega)

private lemma four_dvd_add_one_of_odd_pow_add_one {q n : ℕ} (hq : Odd q) (hn : Odd n)
    (h : 4 ∣ q ^ n + 1) : 4 ∣ q + 1 := by
  have h0 : q ^ n + 1 ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr h
  have hq' : q ^ n ≡ q [MOD 4] := odd_pow_modEq_self q n hq hn
  have h1 : q + 1 ≡ 0 [MOD 4] := (hq'.add (Nat.ModEq.refl 1)).symm.trans h0
  exact Nat.modEq_zero_iff_dvd.mp h1

private lemma exceptionalOrders_four {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (h : 4 ∣ (exceptionalOrders t n p f).1 ∨ 4 ∣ (exceptionalOrders t n p f).2) :
    t = .PSL ∧ n = 3 ∧ p = 2 ∧ f = 2 := by
  unfold exceptionalOrders at h
  split at h <;> simp_all <;> omega

theorem l2_four_dvd_orders (t : CFSG.Open.StatedLieTag) (n p f : ℕ)
    (m : generic t n p f × exceptional t n p f) (hm : 4 ∣ orderOf m) :
    4 ∣ (genericOrders t n p f).1 ∨ 4 ∣ (genericOrders t n p f).2 ∨
      4 ∣ (exceptionalOrders t n p f).1 ∨ 4 ∣ (exceptionalOrders t n p f).2 := by
  have hm' : 4 ∣ (orderOf m.1).lcm (orderOf m.2) := by rwa [Prod.orderOf] at hm
  rcases four_dvd_lcm hm' with hm1 | hm2
  · rw [Prod.orderOf] at hm1
    rcases four_dvd_lcm hm1 with h | h
    · left; exact four_dvd_of_zmod m.1.1 h
    · right; left; exact four_dvd_of_zmod m.1.2 h
  · rw [Prod.orderOf] at hm2
    rcases four_dvd_lcm hm2 with h | h
    · right; right; left; exact four_dvd_of_zmod m.2.1 h
    · right; right; right; exact four_dvd_of_zmod m.2.2 h

theorem l2_orders_cases {X : Type} [Group X] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hX : CFSG.Blueprint.LieModel X t n p f)
    (h4 : 4 ∣ (genericOrders t n p f).1 ∨ 4 ∣ (genericOrders t n p f).2 ∨
      4 ∣ (exceptionalOrders t n p f).1 ∨ 4 ∣ (exceptionalOrders t n p f).2) :
    L2Z4Type X := by
  unfold L2Z4Type
  cases t
  ·
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl ⟨n, p, f, h.trans (Nat.gcd_dvd_left n _),
        h.trans (Nat.gcd_dvd_right n _), hX⟩))
    · exact absurd h (by decide)
    · obtain ⟨-, rfl, rfl, rfl⟩ := exceptionalOrders_four (Or.inl h)
      exact Or.inr (Or.inl hX)
    · obtain ⟨-, rfl, rfl, rfl⟩ := exceptionalOrders_four (Or.inr h)
      exact Or.inr (Or.inl hX)
  ·
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, p, f, h.trans (Nat.gcd_dvd_left n _),
        h.trans (Nat.gcd_dvd_right n _), hX⟩)))
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd (h.trans (Nat.gcd_dvd_left 2 _)) (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · by_cases hq : Even (p ^ f)
      · rw [if_pos hq] at h
        exact absurd h (by decide)
      · rw [if_neg hq] at h
        by_cases hn : Even n
        · rw [if_pos hn] at h
          exact absurd h (by decide)
        · rw [if_neg hn] at h
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, p, f, ?_, ?_, hX⟩))))
          · exact Nat.not_even_iff_odd.mp hn
          · exact four_dvd_sub_one_of_odd_pow (Nat.not_even_iff_odd.mp hq)
              (Nat.not_even_iff_odd.mp hn) (h.trans (Nat.gcd_dvd_right 4 _))
    · by_cases hq : Even (p ^ f)
      · rw [if_pos hq] at h
        exact absurd h (by decide)
      · rw [if_neg hq] at h
        by_cases hn : Even n
        · rw [if_pos hn] at h
          exact absurd h (by decide)
        · rw [if_neg hn] at h
          have h' : 4 ∣ 1 := by simpa using h
          exact absurd h' (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · have hn4 : 4 ≤ n := by simpa using hX.admissible.2.2
      have hn0 : n ≠ 0 := by omega
      have hq : Odd (p ^ f) :=
        odd_of_four_dvd_pow_add_one hn0 (h.trans (Nat.gcd_dvd_right 4 _))
      have hnodd : Odd n := by
        rw [← Nat.not_even_iff_odd]
        intro hne
        exact not_four_dvd_pow_add_one_of_even (p ^ f) hq hne (h.trans (Nat.gcd_dvd_right 4 _))
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, p, f, hnodd, ?_, hX⟩))))
      exact four_dvd_add_one_of_odd_pow_add_one hq hnodd (h.trans (Nat.gcd_dvd_right 4 _))
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd (h.trans (Nat.gcd_dvd_left 3 _)) (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd (h.trans (Nat.gcd_dvd_left 2 _)) (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd (h.trans (Nat.gcd_dvd_left 3 _)) (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)
  ·
    exfalso
    simp only [genericOrders] at h4
    rcases h4 with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd (exceptionalOrders_four (Or.inl h)).1 (by decide)
    · exact absurd (exceptionalOrders_four (Or.inr h)).1 (by decide)

end CFSG.OddStandard.HigherRank.YamadaG23
