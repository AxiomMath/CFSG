module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433Reduction
public import CFSG.Models.PGLSimple
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

open Finset CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420

abbrev L3OrderPlus (s n : ℕ) : Prop :=
  (s + 1) % 3 = 1 ∧ 3 ≤ s ∧ 3 * n = (s + 1) ^ 3 * (s * (s + 2) * (s * (s ^ 2 + 3 * s + 3)))

abbrev L3OrderMinus (s n : ℕ) : Prop :=
  (s + 1) % 3 = 2 ∧ 4 ≤ s ∧ 3 * n = (s + 1) ^ 3 * (s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1)))

abbrev L3Order (p s n : ℕ) : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧ s + 1 = p ^ k) ∧ (L3OrderPlus s n ∨ L3OrderMinus s n)

theorem poly_one {s : ℕ} (hs : 3 ≤ s) :
    3 * (s + 2) ^ 6 ≤ (s + 1) ^ 3 * (s * (s + 2) * (s * (s ^ 2 + 3 * s + 3))) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
  have key : (t + 3 + 1) ^ 3 * ((t + 3) * (t + 3 + 2) * ((t + 3) * ((t + 3) ^ 2 + 3 * (t + 3) + 3)))
      = 3 * (t + 3 + 2) ^ 6 + (t + 3 + 2) * (t ^ 7 + 27 * t ^ 6 + 309 * t ^ 5 + 1924 * t ^ 4
        + 6915 * t ^ 3 + 13830 * t ^ 2 + 12945 * t + 2721) := by ring
  rw [key]
  exact Nat.le_add_right _ _

theorem poly_two {s : ℕ} (hs : 10 ≤ s) :
    24 * (s + 2) ^ 6 ≤ (s + 1) ^ 3 * (s * (s + 2) * (s * (s ^ 2 + 3 * s + 3))) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 10 := ⟨s - 10, by omega⟩
  have key : (t + 10 + 1) ^ 3 * ((t + 10) * (t + 10 + 2) * ((t + 10) * ((t + 10) ^ 2 + 3 * (t + 10) + 3)))
      = 24 * (t + 10 + 2) ^ 6 + (t + 10 + 2) * (11730332 + 8941340 * t + 2747043 * t ^ 2
        + 451212 * t ^ 3 + 43329 * t ^ 4 + 2451 * t ^ 5 + 76 * t ^ 6 + t ^ 7) := by ring
  rw [key]
  exact Nat.le_add_right _ _

theorem poly_minus_ge {s : ℕ} :
    s * (s + 2) * (s * (s ^ 2 + 3 * s + 3)) ≤ s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1)) := by
  apply Nat.mul_le_mul_left
  have key : (s + 2) * (s ^ 2 + s + 1) = s * (s ^ 2 + 3 * s + 3) + 2 := by ring
  rw [key]
  exact Nat.le_add_right _ _

theorem L3Order.size {p s n : ℕ} (h : L3Order p s n) : (s = 3 ∧ n = 20160) ∨ 126000 ≤ n := by
  obtain ⟨-, h1 | h2⟩ := h
  · obtain ⟨h3, hs, hn⟩ := h1
    by_cases hs3 : s = 3
    · subst hs3
      left
      norm_num at hn
      exact ⟨rfl, by omega⟩
    · right
      have hs6 : 6 ≤ s := by omega
      have a1 : 7 ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have a2 : 6 * 8 ≤ s * (s + 2) := Nat.mul_le_mul (by omega) (by omega)
      have a3 : 6 * (6 ^ 2 + 3 * 6 + 3) ≤ s * (s ^ 2 + 3 * s + 3) := by
        apply Nat.mul_le_mul hs6
        have : 6 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs6 2
        omega
      have := Nat.mul_le_mul a1 (Nat.mul_le_mul a2 a3)
      rw [← hn] at this
      norm_num at this
      omega
  · obtain ⟨h3, hs, hn⟩ := h2
    by_cases hs4 : s = 4
    · subst hs4
      right
      norm_num at hn
      omega
    · right
      have hs7 : 7 ≤ s := by omega
      have a1 : 8 ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have a2 : 7 * 9 ≤ s * (s + 2) := Nat.mul_le_mul (by omega) (by omega)
      have a3 : 7 * 9 ≤ (s + 2) * (s ^ 2 + s + 1) := by
        apply Nat.mul_le_mul (by omega)
        have : 7 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      have := Nat.mul_le_mul a1 (Nat.mul_le_mul a2 a3)
      rw [← hn] at this
      norm_num at this
      omega

theorem not_dvd_pow_of_ne {q p k : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p) :
    ¬ q ∣ p ^ k := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))

theorem dvd_three_factors {q v a b c : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hd : q ^ v ∣ a * a * b * c) (hab : Nat.gcd a b ∣ 2) (hac : Nat.gcd a c ∣ 3)
    (hbc : Nat.Coprime b c) : q ^ v ∣ a * a ∨ q ^ v ∣ b ∨ q ^ v ∣ c := by
  have hq2 : ¬ q ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hq3 : ¬ q ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have cop : ∀ x : ℕ, ¬ q ∣ x → Nat.Coprime (q ^ v) x := fun x hx =>
    Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hq).2 hx)
  by_cases ha : q ∣ a
  · have hb : ¬ q ∣ b := fun hb => hq2 ((Nat.dvd_gcd ha hb).trans hab)
    have hc : ¬ q ∣ c := fun hc => hq3 ((Nat.dvd_gcd ha hc).trans hac)
    left
    have h2 : q ^ v ∣ (a * a) * (b * c) := by
      have e : a * a * b * c = (a * a) * (b * c) := by ring
      rw [← e]; exact hd
    exact (Nat.Coprime.mul_right (cop b hb) (cop c hc)).dvd_of_dvd_mul_right h2
  · by_cases hb : q ∣ b
    · have hc : ¬ q ∣ c := fun hc => by
        have h := Nat.dvd_gcd hb hc
        rw [Nat.Coprime.gcd_eq_one hbc] at h
        exact hq.one_lt.ne' (Nat.dvd_one.1 h)
      right; left
      have h2 : q ^ v ∣ b * (a * a * c) := by
        have e : a * a * b * c = b * (a * a * c) := by ring
        rw [← e]; exact hd
      exact (Nat.Coprime.mul_right (Nat.Coprime.mul_right (cop a ha) (cop a ha)) (cop c hc)).dvd_of_dvd_mul_right h2
    · right; right
      have h2 : q ^ v ∣ (a * a * b) * c := hd
      exact (Nat.Coprime.mul_right (Nat.Coprime.mul_right (cop a ha) (cop a ha)) (cop b hb)).dvd_of_dvd_mul_left h2

theorem bound_ge5 {q r a b c n v : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hqr : ¬ q ∣ r)
    (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hn : 3 * n = r ^ 3 * (a * a * b * c))
    (hab : Nat.gcd a b ∣ 2) (hac : Nat.gcd a c ∣ 3) (hbc : Nat.Coprime b c)
    (ha : a ≤ r + 1) (hb : b ≤ r + 1) (hc : c ≤ (r + 1) ^ 2) (hlb : (r + 1) ^ 6 ≤ n)
    (hdiv : q ^ v ∣ n) : q ^ (3 * v) ≤ n := by
  have hcop : Nat.Coprime (q ^ v) (r ^ 3) :=
    Nat.Coprime.pow v 3 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqr)
  have h3 : q ^ v ∣ r ^ 3 * (a * a * b * c) := by
    rw [← hn]; exact Dvd.dvd.mul_left hdiv 3
  have h4 : q ^ v ∣ a * a * b * c := hcop.dvd_of_dvd_mul_left h3
  have hle : q ^ v ≤ (r + 1) ^ 2 := by
    rcases dvd_three_factors hq hq5 h4 hab hac hbc with h | h | h
    · have h1 : q ^ v ≤ a * a := Nat.le_of_dvd (Nat.mul_pos ha0 ha0) h
      have h2 : a * a ≤ (r + 1) * (r + 1) := Nat.mul_le_mul ha ha
      exact h1.trans (h2.trans (le_of_eq (by ring)))
    · have h1 : q ^ v ≤ b := Nat.le_of_dvd hb0 h
      exact h1.trans (hb.trans (Nat.le_self_pow (by norm_num) _))
    · have h1 : q ^ v ≤ c := Nat.le_of_dvd hc0 h
      exact h1.trans hc
  calc q ^ (3 * v) = (q ^ v) ^ 3 := by ring
    _ ≤ ((r + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
    _ = (r + 1) ^ 6 := by ring
    _ ≤ n := hlb

theorem bound_three {r a b c' n v : ℕ} (ha0 : 0 < a) (hr3 : ¬ 3 ∣ r) (hb3 : ¬ 3 ∣ b)
    (hc3 : ¬ 3 ∣ c') (ha : a ≤ r + 1) (hlb : (r + 1) ^ 6 ≤ n)
    (hn : 3 * n = r ^ 3 * (a * a * b * (3 * c'))) (hdiv : 3 ^ v ∣ n) :
    3 ^ (3 * v) ≤ n := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have h1 : 3 * 3 ^ v ∣ 3 * (r ^ 3 * (a * a * b * c')) := by
    have e : 3 * (r ^ 3 * (a * a * b * c')) = r ^ 3 * (a * a * b * (3 * c')) := by ring
    rw [e, ← hn]
    exact mul_dvd_mul_left 3 hdiv
  have h2 : 3 ^ v ∣ r ^ 3 * (a * a * b * c') := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hcop : Nat.Coprime (3 ^ v) (r ^ 3 * (b * c')) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow v 3 ((Nat.Prime.coprime_iff_not_dvd hp3).2 hr3))
      (Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp3).2 hb3 |> Nat.Coprime.pow_left v)
        ((Nat.Prime.coprime_iff_not_dvd hp3).2 hc3 |> Nat.Coprime.pow_left v))
  have h3 : 3 ^ v ∣ a * a := by
    have e : r ^ 3 * (a * a * b * c') = (a * a) * (r ^ 3 * (b * c')) := by ring
    rw [e] at h2
    exact hcop.dvd_of_dvd_mul_right h2
  have hle : 3 ^ v ≤ (r + 1) ^ 2 := by
    have h4 : 3 ^ v ≤ a * a := Nat.le_of_dvd (Nat.mul_pos ha0 ha0) h3
    have h5 : a * a ≤ (r + 1) * (r + 1) := Nat.mul_le_mul ha ha
    exact h4.trans (h5.trans (le_of_eq (by ring)))
  calc 3 ^ (3 * v) = (3 ^ v) ^ 3 := by ring
    _ ≤ ((r + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
    _ = (r + 1) ^ 6 := by ring
    _ ≤ n := hlb

theorem two_split {r a b c n v : ℕ} (hr2 : ¬ 2 ∣ r) (hc2 : ¬ 2 ∣ c) (ha2 : 2 ∣ a) (hb2 : 2 ∣ b)
    (hn : 3 * n = r ^ 3 * (a * a * b * c)) (hrel : a % 4 = 2 ∨ b % 4 = 2) (hdiv : 2 ^ v ∣ n) :
    (a % 4 = 2 ∧ 2 ^ v ∣ 4 * b) ∨ (b % 4 = 2 ∧ 2 ^ v ∣ 2 * (a * a)) := by
  have hp2 : Nat.Prime 2 := Nat.prime_two
  have hcr : Nat.Coprime (2 ^ v) (r ^ 3) :=
    Nat.Coprime.pow v 3 ((Nat.Prime.coprime_iff_not_dvd hp2).2 hr2)
  have hcc : Nat.Coprime (2 ^ v) c := Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp2).2 hc2)
  have h1 : 2 ^ v ∣ r ^ 3 * (a * a * b * c) := by
    rw [← hn]; exact Dvd.dvd.mul_left hdiv 3
  have h2 : 2 ^ v ∣ a * a * b * c := hcr.dvd_of_dvd_mul_left h1
  have h3 : 2 ^ v ∣ a * a * b := hcc.dvd_of_dvd_mul_right h2
  rcases hrel with h | h
  · left
    obtain ⟨α, hα⟩ : ∃ α, a = 2 * α := ⟨a / 2, by omega⟩
    have hαodd : ¬ 2 ∣ α := by omega
    have hcop : Nat.Coprime (2 ^ v) (α * α) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp2).2 hαodd))
        (Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp2).2 hαodd))
    have h4 : 2 ^ v ∣ (α * α) * (4 * b) := by
      have e : a * a * b = (α * α) * (4 * b) := by rw [hα]; ring
      rw [← e]; exact h3
    exact ⟨h, hcop.dvd_of_dvd_mul_left h4⟩
  · right
    obtain ⟨β, hβ⟩ : ∃ β, b = 2 * β := ⟨b / 2, by omega⟩
    have hβodd : ¬ 2 ∣ β := by omega
    have hcop : Nat.Coprime (2 ^ v) β :=
      Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp2).2 hβodd)
    have h4 : 2 ^ v ∣ (2 * (a * a)) * β := by
      have e : a * a * b = (2 * (a * a)) * β := by rw [hβ]; ring
      rw [← e]; exact h3
    exact ⟨h, hcop.dvd_of_dvd_mul_right h4⟩

theorem bound_two {r a b c n v : ℕ} (ha0 : 0 < a) (hb0 : 0 < b) (hr3 : 3 ≤ r) (hr2 : ¬ 2 ∣ r)
    (hc2 : ¬ 2 ∣ c)
    (ha2 : 2 ∣ a) (hb2 : 2 ∣ b) (ha : a ≤ r + 1) (hb : b ≤ r + 1)
    (hn : 3 * n = r ^ 3 * (a * a * b * c)) (hrel : a % 4 = 2 ∨ b % 4 = 2)
    (hlb : (r + 1) ^ 6 ≤ n) (hB : b % 4 = 2 → 8 * (r + 1) ^ 6 ≤ n) (hdiv : 2 ^ v ∣ n) :
    2 ^ (3 * v) ≤ n := by
  rcases two_split hr2 hc2 ha2 hb2 hn hrel hdiv with ⟨-, h⟩ | ⟨hBn, h⟩
  · have h1 : 2 ^ v ≤ 4 * b := Nat.le_of_dvd (by omega) h
    have h3 : 2 ^ v ≤ 4 * (r + 1) := by omega
    have h4 : 64 ≤ (r + 1) ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left (show 4 ≤ r + 1 by omega) 3)
    calc 2 ^ (3 * v) = (2 ^ v) ^ 3 := by ring
      _ ≤ (4 * (r + 1)) ^ 3 := Nat.pow_le_pow_left h3 3
      _ = 64 * (r + 1) ^ 3 := by ring
      _ ≤ (r + 1) ^ 3 * (r + 1) ^ 3 := Nat.mul_le_mul_right _ h4
      _ = (r + 1) ^ 6 := by ring
      _ ≤ n := hlb
  · have h1 : 2 ^ v ≤ 2 * (a * a) := Nat.le_of_dvd (by positivity) h
    have h2 : 2 * (a * a) ≤ 2 * ((r + 1) * (r + 1)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul ha ha)
    calc 2 ^ (3 * v) = (2 ^ v) ^ 3 := by ring
      _ ≤ (2 * ((r + 1) * (r + 1))) ^ 3 := Nat.pow_le_pow_left (h1.trans h2) 3
      _ = 8 * (r + 1) ^ 6 := by ring
      _ ≤ n := hB hBn

theorem gcd_two (x : ℕ) : Nat.gcd x (x + 2) ∣ 2 := by
  have h1 : Nat.gcd x (x + 2) ∣ x := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd x (x + 2) ∣ x + 2 := Nat.gcd_dvd_right _ _
  exact (Nat.dvd_add_right h1).1 h2

theorem gcd_three_plus (x : ℕ) : Nat.gcd x (x ^ 2 + 3 * x + 3) ∣ 3 := by
  have h1 : Nat.gcd x (x ^ 2 + 3 * x + 3) ∣ x := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd x (x ^ 2 + 3 * x + 3) ∣ x ^ 2 + 3 * x + 3 := Nat.gcd_dvd_right _ _
  have e : x ^ 2 + 3 * x + 3 = x * (x + 3) + 3 := by ring
  have h3 : Nat.gcd x (x ^ 2 + 3 * x + 3) ∣ x * (x + 3) + 3 := by rw [← e]; exact h2
  exact (Nat.dvd_add_right (h1.mul_right _)).1 h3

theorem gcd_three_minus (s : ℕ) : Nat.gcd (s + 2) (s ^ 2 + s + 1) ∣ 3 := by
  have h1 : Nat.gcd (s + 2) (s ^ 2 + s + 1) ∣ s + 2 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (s + 2) (s ^ 2 + s + 1) ∣ s ^ 2 + s + 1 := Nat.gcd_dvd_right _ _
  have h3 := dvd_add h2 h1
  have e : s ^ 2 + s + 1 + (s + 2) = (s + 2) * s + 3 := by ring
  rw [e] at h3
  exact (Nat.dvd_add_right (h1.mul_right _)).1 h3

theorem coprime_plus (s : ℕ) : Nat.Coprime (s + 2) (s ^ 2 + 3 * s + 3) := by
  have ha := Nat.gcd_dvd_left (s + 2) (s ^ 2 + 3 * s + 3)
  have hb := Nat.gcd_dvd_right (s + 2) (s ^ 2 + 3 * s + 3)
  have e : s ^ 2 + 3 * s + 3 = 1 + (s + 2) * (s + 1) := by ring
  have hb' : Nat.gcd (s + 2) (s ^ 2 + 3 * s + 3) ∣ 1 + (s + 2) * (s + 1) := by rw [← e]; exact hb
  have h1 : Nat.gcd (s + 2) (s ^ 2 + 3 * s + 3) ∣ 1 := (Nat.dvd_add_left (ha.mul_right (s + 1))).1 hb'
  exact Nat.dvd_one.1 h1

theorem coprime_minus (s : ℕ) : Nat.Coprime s (s ^ 2 + s + 1) := by
  have ha := Nat.gcd_dvd_left s (s ^ 2 + s + 1)
  have hb := Nat.gcd_dvd_right s (s ^ 2 + s + 1)
  have e : s ^ 2 + s + 1 = 1 + s * (s + 1) := by ring
  have hb' : Nat.gcd s (s ^ 2 + s + 1) ∣ 1 + s * (s + 1) := by rw [← e]; exact hb
  have h1 : Nat.gcd s (s ^ 2 + s + 1) ∣ 1 := (Nat.dvd_add_left (ha.mul_right (s + 1))).1 hb'
  exact Nat.dvd_one.1 h1

theorem q_cases {q : ℕ} (hq : q.Prime) : q = 2 ∨ q = 3 ∨ 5 ≤ q := by
  rcases Nat.lt_or_ge q 5 with h | h
  · have := hq.two_le
    interval_cases q <;> first | omega | (norm_num at hq)
  · exact Or.inr (Or.inr h)

theorem qpow_plus {q s n v : ℕ} (hq : q.Prime) (hqr : ¬ q ∣ s + 1) (hs : 3 ≤ s)
    (h3 : (s + 1) % 3 = 1) (hn : 3 * n = (s + 1) ^ 3 * (s * (s + 2) * (s * (s ^ 2 + 3 * s + 3))))
    (hdiv : q ^ v ∣ n) : q ^ (3 * v) ≤ n := by
  have hlb : (s + 1 + 1) ^ 6 ≤ n := by
    have h := poly_one hs
    rw [← hn] at h
    have h' : 3 * (s + 1 + 1) ^ 6 ≤ 3 * n := h
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  rcases q_cases hq with rfl | rfl | hq5
  ·
    have hs2 : 2 ∣ s := by omega
    obtain ⟨u, hu⟩ := hs2
    have hc2 : ¬ 2 ∣ s ^ 2 + 3 * s + 3 := by
      have e : s ^ 2 + 3 * s + 3 = 2 * (2 * u ^ 2 + 3 * u + 1) + 1 := by rw [hu]; ring
      rw [e]; omega
    have hrel : s % 4 = 2 ∨ (s + 2) % 4 = 2 := by omega
    have hB : (s + 2) % 4 = 2 → 8 * (s + 1 + 1) ^ 6 ≤ n := by
      intro hB4
      have hs10 : 10 ≤ s := by omega
      have h := poly_two hs10
      rw [← hn] at h
      have h' : 3 * (8 * (s + 1 + 1) ^ 6) ≤ 3 * n := by
        have e : 3 * (8 * (s + 1 + 1) ^ 6) = 24 * (s + 2) ^ 6 := by ring
        rw [e]; exact h
      exact Nat.le_of_mul_le_mul_left h' (by norm_num)
    have hn' : 3 * n = (s + 1) ^ 3 * (s * s * (s + 2) * (s ^ 2 + 3 * s + 3)) := by
      rw [hn]; ring
    exact bound_two (r := s + 1) (a := s) (b := s + 2) (c := s ^ 2 + 3 * s + 3) (n := n) (v := v)
      (by omega) (by omega) (by omega) hqr hc2 (by omega) (by omega) (by omega) (by omega)
      hn' hrel hlb hB hdiv
  ·
    obtain ⟨k, hk⟩ : ∃ k, s = 3 * k := ⟨s / 3, by omega⟩
    subst hk
    have hk1 : 1 ≤ k := by omega
    have hc3 : ¬ 3 ∣ 3 * k ^ 2 + 3 * k + 1 := by omega
    have hn' : 3 * n = (3 * k + 1) ^ 3 * (3 * k * (3 * k) * (3 * k + 2) * (3 * (3 * k ^ 2 + 3 * k + 1))) := by
      rw [hn]; ring
    exact bound_three (r := 3 * k + 1) (a := 3 * k) (b := 3 * k + 2) (c' := 3 * k ^ 2 + 3 * k + 1)
      (n := n) (v := v) (by omega) (by omega) (by omega) hc3 (by omega) hlb hn' hdiv
  · have ha0 : 0 < s := by omega
    have hc : s ^ 2 + 3 * s + 3 ≤ (s + 1 + 1) ^ 2 := by nlinarith
    exact bound_ge5 (r := s + 1) (a := s) (b := s + 2) (c := s ^ 2 + 3 * s + 3) (n := n) (v := v)
      hq hq5 hqr ha0 (by omega) (by positivity) (by rw [hn]; ring) (gcd_two s) (gcd_three_plus s)
      (coprime_plus s) (by omega) (by omega) hc hlb hdiv

theorem qpow_minus {q s n v : ℕ} (hq : q.Prime) (hqr : ¬ q ∣ s + 1) (hs : 4 ≤ s)
    (h3 : (s + 1) % 3 = 2) (hn : 3 * n = (s + 1) ^ 3 * (s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1))))
    (hdiv : q ^ v ∣ n) : q ^ (3 * v) ≤ n := by
  have hlb : (s + 1 + 1) ^ 6 ≤ n := by
    have h := poly_one (show 3 ≤ s by omega)
    have hm := Nat.mul_le_mul_left ((s + 1) ^ 3) (poly_minus_ge (s := s))
    rw [← hn] at hm
    have h' : 3 * (s + 1 + 1) ^ 6 ≤ 3 * n := h.trans hm
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  rcases q_cases hq with rfl | rfl | hq5
  ·
    have hs2 : 2 ∣ s := by omega
    obtain ⟨u, hu⟩ := hs2
    have hc2 : ¬ 2 ∣ s ^ 2 + s + 1 := by
      have e : s ^ 2 + s + 1 = 2 * (2 * u ^ 2 + u) + 1 := by rw [hu]; ring
      rw [e]; omega
    have hrel : (s + 2) % 4 = 2 ∨ s % 4 = 2 := by omega
    have hB : s % 4 = 2 → 8 * (s + 1 + 1) ^ 6 ≤ n := by
      intro hB4
      have hs10 : 10 ≤ s := by omega
      have h := poly_two hs10
      have hm := Nat.mul_le_mul_left ((s + 1) ^ 3) (poly_minus_ge (s := s))
      rw [← hn] at hm
      have h' : 3 * (8 * (s + 1 + 1) ^ 6) ≤ 3 * n := by
        have e : 3 * (8 * (s + 1 + 1) ^ 6) = 24 * (s + 2) ^ 6 := by ring
        rw [e]; exact h.trans hm
      exact Nat.le_of_mul_le_mul_left h' (by norm_num)
    have hn' : 3 * n = (s + 1) ^ 3 * ((s + 2) * (s + 2) * s * (s ^ 2 + s + 1)) := by
      rw [hn]; ring
    exact bound_two (r := s + 1) (a := s + 2) (b := s) (c := s ^ 2 + s + 1) (n := n) (v := v)
      (by omega) (by omega) (by omega) hqr hc2 (by omega) (by omega) (by omega) (by omega)
      hn' hrel hlb hB hdiv
  ·
    obtain ⟨k, hk⟩ : ∃ k, s = 3 * k + 1 := ⟨s / 3, by omega⟩
    subst hk
    have hc3 : ¬ 3 ∣ 3 * k ^ 2 + 3 * k + 1 := by omega
    have hn' : 3 * n = (3 * k + 1 + 1) ^ 3 *
        ((3 * k + 1 + 2) * (3 * k + 1 + 2) * (3 * k + 1) * (3 * (3 * k ^ 2 + 3 * k + 1))) := by
      rw [hn]; ring
    exact bound_three (r := 3 * k + 1 + 1) (a := 3 * k + 1 + 2) (b := 3 * k + 1)
      (c' := 3 * k ^ 2 + 3 * k + 1) (n := n) (v := v) (by omega) (by omega) (by omega) hc3
      (by omega) hlb hn' hdiv
  · have ha0 : 0 < s := by omega
    have hc : s ^ 2 + s + 1 ≤ (s + 1 + 1) ^ 2 := by nlinarith
    exact bound_ge5 (r := s + 1) (a := s + 2) (b := s) (c := s ^ 2 + s + 1) (n := n) (v := v)
      hq hq5 hqr (by omega) ha0 (by positivity) (by rw [hn]; ring)
      (by rw [Nat.gcd_comm]; exact gcd_two s) (gcd_three_minus s) (coprime_minus s)
      (by omega) (by omega) hc hlb hdiv

theorem qpow_bound {p s n q v : ℕ} (hq : q.Prime) (hp : p.Prime) (hqp : q ≠ p)
    (hL : L3Order p s n) (hdiv : q ^ v ∣ n) : q ^ (3 * v) ≤ n := by
  obtain ⟨⟨k, -, hk⟩, h⟩ := hL
  have hqr : ¬ q ∣ s + 1 := by rw [hk]; exact not_dvd_pow_of_ne hq hp hqp
  rcases h with h | h
  · exact qpow_plus hq hqr h.2.1 h.1 h.2.2 hdiv
  · exact qpow_minus hq hqr h.2.1 h.1 h.2.2 hdiv


theorem sub_one_le_pow' (Q a : ℕ) : Q ^ a - 1 ≤ Q ^ a := Nat.sub_le _ _

theorem add_one_le_pow' {Q : ℕ} (hQ : 2 ≤ Q) (a : ℕ) : Q ^ a + 1 ≤ Q ^ (a + 1) := by
  rw [pow_succ]
  have : 1 ≤ Q ^ a := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem mul_le_pow_add' {X Y Q a b : ℕ} (hX : X ≤ Q ^ a) (hY : Y ≤ Q ^ b) :
    X * Y ≤ Q ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hX hY

theorem part_of_shape {p Q N Y c n e : ℕ} (hQ : Q = p ^ e) (hn : n = Q ^ N * Y / c) (hc : c ∣ Y)
    (hY : Y < Q ^ (2 * N)) : ∃ v M : ℕ, n = p ^ v * M ∧ M < p ^ (2 * v) := by
  refine ⟨e * N, Y / c, ?_, ?_⟩
  · rw [hn, Nat.mul_div_assoc _ hc, hQ, ← pow_mul]
  · calc Y / c ≤ Y := Nat.div_le_self _ _
      _ < Q ^ (2 * N) := hY
      _ = p ^ (2 * (e * N)) := by rw [hQ, ← pow_mul]; congr 1; ring

theorem sum_Icc_two (n : ℕ) : 2 * ∑ i ∈ Icc 2 (n + 1), i = n * n + 3 * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1)]
    nlinarith [ih]

theorem sum_Icc_two_succ (n : ℕ) : 2 * ∑ i ∈ Icc 2 (n + 1), (i + 1) = n * n + 5 * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1)]
    nlinarith [ih]

theorem sum_Icc_one (n : ℕ) : ∑ i ∈ Icc 1 n, 2 * i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    nlinarith [ih]

theorem two_mul_tri (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)

theorem prod_le_pow_sum {Q : ℕ} {s : Finset ℕ} {f g : ℕ → ℕ} (h : ∀ i ∈ s, f i ≤ Q ^ g i) :
    ∏ i ∈ s, f i ≤ Q ^ (∑ i ∈ s, g i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' h

theorem dvd_sq_sub_one {Q : ℕ} (hQ : 1 ≤ Q) : Q - 1 ∣ Q ^ 2 - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 1 := ⟨Q - 1, by omega⟩
  have e : (t + 1) ^ 2 - 1 = t * (t + 2) := by
    rw [show (t + 1) ^ 2 = t * (t + 2) + 1 by ring]; simp
  rw [Nat.add_sub_cancel, e]
  exact dvd_mul_right t (t + 2)

theorem succ_dvd_sq_sub_one {Q : ℕ} (hQ : 1 ≤ Q) : Q + 1 ∣ Q ^ 2 - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 1 := ⟨Q - 1, by omega⟩
  have e : (t + 1) ^ 2 - 1 = (t + 1 + 1) * t := by
    rw [show (t + 1) ^ 2 = (t + 1 + 1) * t + 1 by ring]; simp
  rw [e]
  exact dvd_mul_right _ _

theorem sq_sub_one_dvd_prod (n Q : ℕ) (hn : 1 ≤ n) :
    Q ^ 2 - 1 ∣ ∏ i ∈ Icc 2 (n + 1), (Q ^ i - 1) :=
  Finset.dvd_prod_of_mem (fun i => Q ^ i - 1) (by simp; omega)

theorem shape_A (n Q : ℕ) (hn : 1 ≤ n) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderA n Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨n * (n + 1) / 2, ∏ i ∈ Icc 2 (n + 1), (Q ^ i - 1), Nat.gcd (n + 1) (Q - 1), ?_, rfl, ?_, ?_⟩
  · apply Nat.div_pos _ (by norm_num)
    nlinarith
  · exact (Nat.gcd_dvd_right _ _).trans ((dvd_sq_sub_one (by omega)).trans (sq_sub_one_dvd_prod n Q hn))
  · rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp only [Finset.Icc_self, Finset.prod_singleton]
      have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      show Q ^ 2 - 1 < Q ^ (2 * (1 * (1 + 1) / 2))
      norm_num
      omega
    · have hS := sum_Icc_two n
      have hN := two_mul_tri n
      have hY : ∏ i ∈ Icc 2 (n + 1), (Q ^ i - 1) ≤ Q ^ (∑ i ∈ Icc 2 (n + 1), i) :=
        prod_le_pow_sum (fun i _ => sub_one_le_pow' Q i)
      have hlt : ∑ i ∈ Icc 2 (n + 1), i < 2 * (n * (n + 1) / 2) := by
        nlinarith
      exact lt_of_le_of_lt hY (Nat.pow_lt_pow_right (by omega) hlt)

theorem shape_twistedA (n Q : ℕ) (hn : 2 ≤ n) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderTwistedA n Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨n * (n + 1) / 2, ∏ i ∈ Icc 2 (n + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1),
    Nat.gcd (n + 1) (Q + 1), ?_, rfl, ?_, ?_⟩
  · apply Nat.div_pos _ (by norm_num)
    nlinarith
  · have h2 : (if Even 2 then Q ^ 2 - 1 else Q ^ 2 + 1) ∣
        ∏ i ∈ Icc 2 (n + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1) :=
      Finset.dvd_prod_of_mem (fun i => if Even i then Q ^ i - 1 else Q ^ i + 1) (by simp; omega)
    simp only [even_two, if_true] at h2
    exact (Nat.gcd_dvd_right _ _).trans ((succ_dvd_sq_sub_one (by omega)).trans h2)
  · have hN := two_mul_tri n
    rcases Nat.lt_or_ge n 3 with h | h
    ·
      obtain rfl : n = 2 := by omega
      have h2 : ∏ i ∈ Icc 2 (2 + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1)
          = (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
        rw [show Icc 2 (2 + 1) = {2, 3} from by decide, Finset.prod_pair (by norm_num)]
        simp [Nat.even_iff]
      rw [h2]
      show (Q ^ 2 - 1) * (Q ^ 3 + 1) < Q ^ 6
      have h3 : Q ^ 3 + 1 ≤ Q ^ 4 := by
        have := add_one_le_pow' hQ 3
        simpa using this
      have h4 : Q ^ 2 - 1 < Q ^ 2 := Nat.sub_lt (by positivity) one_pos
      calc (Q ^ 2 - 1) * (Q ^ 3 + 1) ≤ (Q ^ 2 - 1) * Q ^ 4 := Nat.mul_le_mul_left _ h3
        _ < Q ^ 2 * Q ^ 4 := Nat.mul_lt_mul_of_pos_right h4 (by positivity)
        _ = Q ^ 6 := by ring
    · rcases Nat.lt_or_ge n 4 with h' | h'
      ·
        obtain rfl : n = 3 := by omega
        have hY : ∏ i ∈ Icc 2 (3 + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1)
            ≤ Q ^ (∑ i ∈ Icc 2 (3 + 1), (if Even i then i else i + 1)) := by
          apply prod_le_pow_sum
          intro i _
          split_ifs
          · exact sub_one_le_pow' Q i
          · exact add_one_le_pow' hQ i
        have hsum : ∑ i ∈ Icc 2 (3 + 1), (if Even i then i else i + 1) = 10 := by decide
        rw [hsum] at hY
        exact lt_of_le_of_lt hY (Nat.pow_lt_pow_right (by omega) (by norm_num))
      ·
        have hS := sum_Icc_two_succ n
        have hY : ∏ i ∈ Icc 2 (n + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1)
            ≤ Q ^ (∑ i ∈ Icc 2 (n + 1), (i + 1)) := by
          apply prod_le_pow_sum
          intro i _
          split_ifs
          · exact (sub_one_le_pow' Q i).trans (Nat.pow_le_pow_right (by omega) (by omega))
          · exact add_one_le_pow' hQ i
        have hlt : ∑ i ∈ Icc 2 (n + 1), (i + 1) < 2 * (n * (n + 1) / 2) := by
          nlinarith
        exact lt_of_le_of_lt hY (Nat.pow_lt_pow_right (by omega) hlt)

theorem shape_BC (n Q : ℕ) (hn : 2 ≤ n) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderBC n Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨n * n, ∏ i ∈ Icc 1 n, (Q ^ (2 * i) - 1), Nat.gcd 2 (Q - 1), ?_, rfl, ?_, ?_⟩
  · nlinarith
  · have h1 : (fun i => Q ^ (2 * i) - 1) 1 ∣ ∏ i ∈ Icc 1 n, (Q ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i => Q ^ (2 * i) - 1) (by simp; omega)
    simp only [mul_one] at h1
    exact (Nat.gcd_dvd_right _ _).trans ((dvd_sq_sub_one (by omega)).trans h1)
  · have hY : ∏ i ∈ Icc 1 n, (Q ^ (2 * i) - 1) ≤ Q ^ (∑ i ∈ Icc 1 n, 2 * i) :=
      prod_le_pow_sum (fun i _ => sub_one_le_pow' Q (2 * i))
    rw [sum_Icc_one] at hY
    exact lt_of_le_of_lt hY (Nat.pow_lt_pow_right (by omega) (by nlinarith))

theorem shape_D (m Q : ℕ) (hm : 3 ≤ m) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderD (m + 1) Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨(m + 1) * m, (Q ^ (m + 1) - 1) * ∏ i ∈ Icc 1 m, (Q ^ (2 * i) - 1),
    Nat.gcd 4 (Q ^ (m + 1) - 1), ?_, ?_, ?_, ?_⟩
  · nlinarith
  · simp only [orderD, Nat.add_sub_cancel, mul_assoc]
  · exact Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _
  · have hP : ∏ i ∈ Icc 1 m, (Q ^ (2 * i) - 1) ≤ Q ^ (∑ i ∈ Icc 1 m, 2 * i) :=
      prod_le_pow_sum (fun i _ => sub_one_le_pow' Q (2 * i))
    rw [sum_Icc_one] at hP
    have hY : (Q ^ (m + 1) - 1) * ∏ i ∈ Icc 1 m, (Q ^ (2 * i) - 1) ≤ Q ^ (m + 1) * Q ^ (m * (m + 1)) :=
      Nat.mul_le_mul (sub_one_le_pow' Q (m + 1)) hP
    rw [← pow_add] at hY
    exact lt_of_le_of_lt hY (Nat.pow_lt_pow_right (by omega) (by nlinarith))

theorem shape_twistedD (m Q : ℕ) (hm : 3 ≤ m) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderTwistedD (m + 1) Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨(m + 1) * m, (Q ^ (m + 1) + 1) * ∏ i ∈ Icc 1 m, (Q ^ (2 * i) - 1),
    Nat.gcd 4 (Q ^ (m + 1) + 1), ?_, ?_, ?_, ?_⟩
  · nlinarith
  · simp only [orderTwistedD, Nat.add_sub_cancel, mul_assoc]
  · exact Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _
  · have hP : ∏ i ∈ Icc 1 m, (Q ^ (2 * i) - 1) ≤ Q ^ (∑ i ∈ Icc 1 m, 2 * i) :=
      prod_le_pow_sum (fun i _ => sub_one_le_pow' Q (2 * i))
    rw [sum_Icc_one] at hP
    have hY : (Q ^ (m + 1) + 1) * ∏ i ∈ Icc 1 m, (Q ^ (2 * i) - 1)
        ≤ Q ^ (m + 1 + 1) * Q ^ (m * (m + 1)) :=
      Nat.mul_le_mul (add_one_le_pow' hQ (m + 1)) hP
    rw [← pow_add] at hY
    exact lt_of_le_of_lt hY (Nat.pow_lt_pow_right (by omega) (by nlinarith))

theorem shape_E6 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderE6 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨36, (Q ^ 12 - 1) * (Q ^ 9 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 - 1) * (Q ^ 2 - 1),
    Nat.gcd 3 (Q - 1), by norm_num, ?_, ?_, ?_⟩
  · simp only [orderE6, mul_assoc]
  · exact dvd_mul_of_dvd_right ((Nat.gcd_dvd_right _ _).trans (dvd_sq_sub_one (by omega))) _
  · have h := mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add'
      (sub_one_le_pow' Q 12) (sub_one_le_pow' Q 9)) (sub_one_le_pow' Q 8))
      (sub_one_le_pow' Q 6)) (sub_one_le_pow' Q 5)) (sub_one_le_pow' Q 2)
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_twistedE6 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderTwistedE6 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨36, (Q ^ 12 - 1) * (Q ^ 9 + 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 + 1) * (Q ^ 2 - 1),
    Nat.gcd 3 (Q + 1), by norm_num, ?_, ?_, ?_⟩
  · simp only [orderTwistedE6, mul_assoc]
  · exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _ |>.trans (succ_dvd_sq_sub_one (by omega))) _
  · have h := mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add'
      (sub_one_le_pow' Q 12) (add_one_le_pow' hQ 9)) (sub_one_le_pow' Q 8))
      (sub_one_le_pow' Q 6)) (add_one_le_pow' hQ 5)) (sub_one_le_pow' Q 2)
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_E7 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderE7 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨63, (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 10 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) *
    (Q ^ 2 - 1), Nat.gcd 2 (Q - 1), by norm_num, ?_, ?_, ?_⟩
  · simp only [orderE7, mul_assoc]
  · exact dvd_mul_of_dvd_right ((Nat.gcd_dvd_right _ _).trans (dvd_sq_sub_one (by omega))) _
  · have h := mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add'
      (mul_le_pow_add' (sub_one_le_pow' Q 18) (sub_one_le_pow' Q 14)) (sub_one_le_pow' Q 12))
      (sub_one_le_pow' Q 10)) (sub_one_le_pow' Q 8)) (sub_one_le_pow' Q 6)) (sub_one_le_pow' Q 2)
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_E8 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderE8 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨120, (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) * (Q ^ 14 - 1) *
    (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 2 - 1), 1, by norm_num, ?_, one_dvd _, ?_⟩
  · simp only [orderE8, mul_assoc, Nat.div_one]
  · have h := mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add'
      (mul_le_pow_add' (mul_le_pow_add' (sub_one_le_pow' Q 30) (sub_one_le_pow' Q 24))
      (sub_one_le_pow' Q 20)) (sub_one_le_pow' Q 18)) (sub_one_le_pow' Q 14))
      (sub_one_le_pow' Q 12)) (sub_one_le_pow' Q 8)) (sub_one_le_pow' Q 2)
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_F4 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderF4 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨24, (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1), 1, by norm_num, ?_, one_dvd _, ?_⟩
  · simp only [orderF4, mul_assoc, Nat.div_one]
  · have h := mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' (sub_one_le_pow' Q 12)
      (sub_one_le_pow' Q 8)) (sub_one_le_pow' Q 6)) (sub_one_le_pow' Q 2)
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_G2 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderG2 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨6, (Q ^ 6 - 1) * (Q ^ 2 - 1), 1, by norm_num, ?_, one_dvd _, ?_⟩
  · simp only [orderG2, mul_assoc, Nat.div_one]
  · have h := mul_le_pow_add' (sub_one_le_pow' Q 6) (sub_one_le_pow' Q 2)
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_trialityD4 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderTrialityD4 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨12, (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1), 1, by norm_num, ?_, one_dvd _, ?_⟩
  · simp only [orderTrialityD4, mul_assoc, Nat.div_one]
  · have h9 : Q ^ 8 + Q ^ 4 + 1 ≤ Q ^ 9 := by
      have h4 : 2 ≤ Q ^ 4 := le_trans hQ (Nat.le_self_pow (by norm_num) Q)
      have h8 : Q ^ 8 = Q ^ 4 * Q ^ 4 := by ring
      have h9' : Q ^ 9 = Q ^ 8 * Q := by ring
      nlinarith
    have h := mul_le_pow_add' (mul_le_pow_add' h9 (sub_one_le_pow' Q 6)) (sub_one_le_pow' Q 2)
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_suzuki (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderSuzuki Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨2, (Q ^ 2 + 1) * (Q - 1), 1, by norm_num, ?_, one_dvd _, ?_⟩
  · simp only [orderSuzuki, mul_assoc, Nat.div_one]
  · have h3 : Q ^ 2 + 1 ≤ Q ^ 3 := by
      have : Q ^ 3 = Q ^ 2 * Q := by ring
      nlinarith
    have hlt : Q - 1 < Q := Nat.sub_lt (by omega) one_pos
    calc (Q ^ 2 + 1) * (Q - 1) ≤ Q ^ 3 * (Q - 1) := Nat.mul_le_mul_right _ h3
      _ < Q ^ 3 * Q := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
      _ = Q ^ (2 * 2) := by ring

theorem shape_ree (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderRee Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨3, (Q ^ 3 + 1) * (Q - 1), 1, by norm_num, ?_, one_dvd _, ?_⟩
  · simp only [orderRee, mul_assoc, Nat.div_one]
  · have h4 : Q ^ 3 + 1 ≤ Q ^ 4 := by
      have := add_one_le_pow' hQ 3
      simpa using this
    have hlt : Q - 1 < Q := Nat.sub_lt (by omega) one_pos
    have hY : (Q ^ 3 + 1) * (Q - 1) < Q ^ 5 := by
      calc (Q ^ 3 + 1) * (Q - 1) ≤ Q ^ 4 * (Q - 1) := Nat.mul_le_mul_right _ h4
        _ < Q ^ 4 * Q := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
        _ = Q ^ 5 := by ring
    exact lt_of_lt_of_le hY (Nat.pow_le_pow_right (by omega) (by norm_num))

theorem shape_twistedF4 (Q : ℕ) (hQ : 2 ≤ Q) :
    ∃ N Y c : ℕ, 1 ≤ N ∧ orderTwistedF4 Q = Q ^ N * Y / c ∧ c ∣ Y ∧ Y < Q ^ (2 * N) := by
  refine ⟨12, (Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1), 1, by norm_num, ?_, one_dvd _, ?_⟩
  · simp only [orderTwistedF4, mul_assoc, Nat.div_one]
  · have h7 : Q ^ 6 + 1 ≤ Q ^ 7 := by simpa using add_one_le_pow' hQ 6
    have h4' : Q ^ 3 + 1 ≤ Q ^ 4 := by simpa using add_one_le_pow' hQ 3
    have h1 : Q - 1 ≤ Q ^ 1 := by rw [pow_one]; exact Nat.sub_le _ _
    have h := mul_le_pow_add' (mul_le_pow_add' (mul_le_pow_add' h7 (sub_one_le_pow' Q 4)) h4') h1
    exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by omega) (by norm_num))

theorem shape_tits : orderTits = 2 ^ 11 * 8775 ∧ 8775 < 2 ^ (2 * 11) := by
  unfold orderTits; norm_num

theorem card_ge_two (q : TauCeti.PrimePower) : 2 ≤ q.card := by
  rw [TauCeti.PrimePower.card_def]
  exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)

theorem lie_char_part (d : TauCeti.LieTypeIndex) (hd : d.Valid) :
    ∃ v M : ℕ, lieOrderFormula d = d.characteristic ^ v * M ∧ M < d.characteristic ^ (2 * v) := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_A n q.card hs.1 (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_A] <;> assumption
  | twistedA n q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_twistedA n q.card hs.1 (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_twistedA] <;> assumption
  | B n q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_BC n q.card hs.1 (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_B] <;> assumption
  | C n q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_BC n q.card (by omega) (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_C] <;> assumption
  | D n q =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_D m q.card (by omega) (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_D] <;> assumption
  | twistedD n q =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_twistedD m q.card (by omega) (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_twistedD] <;> assumption
  | E6 q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_E6 q.card (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_E6] <;> assumption
  | E7 q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_E7 q.card (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_E7] <;> assumption
  | E8 q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_E8 q.card (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_E8] <;> assumption
  | F4 q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_F4 q.card (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_F4] <;> assumption
  | G2 q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_G2 q.card (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_G2] <;> assumption
  | twistedE6 q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_twistedE6 q.card (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_twistedE6] <;> assumption
  | trialityD4 q =>
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_trialityD4 q.card (card_ge_two q)
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := q.p) (e := q.exponent) (Q := q.card) (TauCeti.PrimePower.card_def q) hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_trialityD4] <;> assumption
  | suzuki m =>
    have hQ : 2 ≤ 2 ^ (2 * m + 1) := Nat.le_self_pow (by omega) 2
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_suzuki (2 ^ (2 * m + 1)) hQ
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := 2) (e := 2 * m + 1) (Q := 2 ^ (2 * m + 1)) rfl hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_suzuki] <;> assumption
  | reeG2 m =>
    have hQ : 2 ≤ 3 ^ (2 * m + 1) := le_trans (by norm_num) (Nat.le_self_pow (by omega) 3)
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_ree (3 ^ (2 * m + 1)) hQ
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := 3) (e := 2 * m + 1) (Q := 3 ^ (2 * m + 1)) rfl hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_reeG2] <;> assumption
  | reeF4 m =>
    have hQ : 2 ≤ 2 ^ (2 * m + 1) := Nat.le_self_pow (by omega) 2
    obtain ⟨N, Y, c, -, hsh, hc, hY⟩ := shape_twistedF4 (2 ^ (2 * m + 1)) hQ
    obtain ⟨v, M, h1, h2⟩ := part_of_shape (p := 2) (e := 2 * m + 1) (Q := 2 ^ (2 * m + 1)) rfl hsh hc hY
    refine ⟨v, M, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_reeF4] <;> assumption
  | tits =>
    obtain ⟨h1, h2⟩ := shape_tits
    refine ⟨11, 8775, ?_, ?_⟩ <;> simp only [lieOrderFormula, TauCeti.LieTypeIndex.characteristic_tits] <;> assumption

theorem card_eq_pow_of_charP (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card K = p ^ k := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, h⟩ := FiniteField.card K p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, h]⟩

theorem card_center_transfer {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

noncomputable def sl3Equiv (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K ≃* CFSG.Open.StatedSL 3 K :=
  (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
    (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 K).symm)

theorem sl_quot_card (K : Type) [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) {W : Type}
    [Group W] [Finite W] (e : W ≃* CFSG.Open.StatedSL 3 K) :
    Nat.card (W ⧸ Subgroup.center W) * 3 =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  have hZ : Nat.card (Subgroup.center W) = 3 := by
    rw [card_center_transfer e, CFSG.Open.StatedCenterThree.card_center_statedSL_three h3]
  have hW := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center W)
  rw [hZ, Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three] at hW
  rw [← hW]

theorem sl_quot_simple (K : Type) [Field K] [Finite K] {W : Type} [Group W]
    (e : W ≃* CFSG.Open.StatedSL 3 K) : IsSimpleGroup (W ⧸ Subgroup.center W) := by
  haveI : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  let e' : W ≃* Matrix.SpecialLinearGroup (Fin 3) K := e.trans (sl3Equiv K).symm
  let e2 : W ⧸ Subgroup.center W ≃* Matrix.SpecialLinearGroup (Fin 3) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
    QuotientGroup.congr (Subgroup.center W) (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) e'
      (Subgroup.map_center_eq e')
  let e3 : Matrix.SpecialLinearGroup (Fin 3) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K).symm).trans
      (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K)
  exact (e2.trans e3).isSimpleGroup

theorem center_statedSU_eq (K : Type) [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : q ≠ 0) (h3 : 3 ∣ q + 1) :
    Subgroup.center (CFSG.Open.StatedSU 3 q K) =
      (CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSU 3 q K) := by
  have hle := CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center (CFSG.Open.StatedSU 3 q K)
  have hK1 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
      rw [Nat.add_sub_cancel, show (t + 1) ^ 2 = (t + 1 + 1) * t + 1 by ring]
      simp
    rw [e]; exact Dvd.dvd.mul_right h3 _
  have hR : Nat.card (rootsOfUnity 3 K) = 3 :=
    CFSG.Open.StatedCenterThree.card_rootsOfUnity_three hK1
  have hmem : ∀ ζ : rootsOfUnity 3 K,
      Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Kˣ) ∈ CFSG.Open.StatedSU 3 q K := fun ζ =>
    CFSG.Open.StatedCenterThree.scalar_mem hq h3 ((mem_rootsOfUnity 3 (ζ : Kˣ)).mp ζ.2)
  have hscal : ∀ ζ : rootsOfUnity 3 K,
      ((⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Kˣ), hmem ζ⟩ :
        ↥(CFSG.Open.StatedSU 3 q K)) ∈
        (CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSU 3 q K)) := fun ζ => by
    rw [Subgroup.mem_subgroupOf]
    unfold CFSG.Open.StatedScalars
    exact MonoidHom.mem_range.2 ⟨(ζ : Kˣ), rfl⟩
  have hinj : Nat.card (rootsOfUnity 3 K) ≤
      Nat.card ((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSU 3 q K)) := by
    refine Nat.card_le_card_of_injective
      (fun ζ => (⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Kˣ), hmem ζ⟩, hscal ζ⟩ :
        ↥((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSU 3 q K)))) ?_
    intro ζ₁ ζ₂ h
    have h' := congrArg (fun z : ↥((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf
        (CFSG.Open.StatedSU 3 q K)) => ((((z : ↥(CFSG.Open.StatedSU 3 q K)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) 0 0)) h
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h'
    exact Subtype.ext (Units.ext h')
  have hcard : Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 q K)) ≤
      Nat.card ((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSU 3 q K)) := by
    exact (CFSG.Open.StatedCenterThree.card_center_statedSU_three hK h3).le.trans
      (hR.symm.le.trans hinj)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem psu_card_three (p j : ℕ) [Fact p.Prime] (hj : 1 ≤ j) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ j) ^ 2) (hq : (p ^ j) % 3 = 2) :
    3 * Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ j) K)) =
      (p ^ j) ^ 3 * (((p ^ j) ^ 2 - 1) * ((p ^ j) ^ 3 + 1)) := by
  have hq1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have h3 : 3 ∣ p ^ j + 1 := by omega
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K)
    (p := p) (f := j) (n := 3) Fact.out hj hK (by norm_num)
  rw [hcard, Nat.gcd_eq_left h3]
  have hprod : ∏ i ∈ Finset.Icc 2 3, ((((p ^ j : ℕ)) : ℤ) ^ i - (-1) ^ i).toNat =
      ((p ^ j) ^ 2 - 1) * ((p ^ j) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by norm_num)]
    have e2 : ((((p ^ j : ℕ)) : ℤ) ^ 2 - (-1) ^ 2).toNat = (p ^ j) ^ 2 - 1 := by
      have : ((((p ^ j : ℕ)) : ℤ) ^ 2 - (-1) ^ 2) = (((p ^ j) ^ 2 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by positivity)), Nat.cast_pow, Nat.cast_pow]
        push_cast; ring
      rw [this, Int.toNat_natCast]
    have e3 : ((((p ^ j : ℕ)) : ℤ) ^ 3 - (-1) ^ 3).toNat = (p ^ j) ^ 3 + 1 := by
      have : ((((p ^ j : ℕ)) : ℤ) ^ 3 - (-1) ^ 3) = (((p ^ j) ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [e2, e3]
  rw [hprod]
  have hdiv : 3 ∣ (p ^ j) ^ (3 * (3 - 1) / 2) * (((p ^ j) ^ 2 - 1) * ((p ^ j) ^ 3 + 1)) := by
    apply Dvd.dvd.mul_left
    apply Dvd.dvd.mul_left
    have : (p ^ j) ^ 3 % 3 = 2 := by
      rw [Nat.pow_mod, hq]
    have h' : ((p ^ j) ^ 3 + 1) % 3 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero h'
  rw [Nat.mul_div_cancel' hdiv]

theorem su_quot_facts (p j : ℕ) [Fact p.Prime] (hj : 1 ≤ j) (hq : (p ^ j) % 3 = 2)
    (hq2 : p ^ j ≠ 2) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ j) ^ 2)
    (W : Type) [Group W] [Finite W] (e : W ≃* CFSG.Open.StatedSU 3 (p ^ j) K) :
    Nat.card (W ⧸ Subgroup.center W) =
        Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ j) K)) ∧
      IsSimpleGroup (W ⧸ Subgroup.center W) := by
  have hq0 : p ^ j ≠ 0 := (pow_pos (Fact.out : p.Prime).pos j).ne'
  have h3 : 3 ∣ p ^ j + 1 := by omega
  have hc := center_statedSU_eq K hK hq0 h3
  haveI : (CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSU 3 (p ^ j) K) |>.Normal := by
    rw [← hc]; infer_instance
  let e2 : W ⧸ Subgroup.center W ≃* CFSG.Open.StatedSU 3 (p ^ j) K ⧸
      Subgroup.center (CFSG.Open.StatedSU 3 (p ^ j) K) :=
    QuotientGroup.congr (Subgroup.center W) (Subgroup.center (CFSG.Open.StatedSU 3 (p ^ j) K)) e
      (Subgroup.map_center_eq e)
  let e3 : CFSG.Open.StatedSU 3 (p ^ j) K ⧸ Subgroup.center (CFSG.Open.StatedSU 3 (p ^ j) K) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ j) K) :=
    QuotientGroup.quotientMulEquivOfEq hc
  have hsimple : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ j) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p j hK 3 le_rfl
      (by intro h; exact hq2 (Prod.mk.inj h).2)
  exact ⟨Nat.card_congr (e2.trans e3).toEquiv, (e2.trans e3).isSimpleGroup⟩

theorem quot_center_cases (H : Type) [Group H] [Finite H] [IsSimpleGroup H] :
    Nat.card (H ⧸ Subgroup.center H) = 1 ∨ Nat.card (H ⧸ Subgroup.center H) = Nat.card H := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · right
    rw [h]
    exact Subgroup.index_bot
  · left
    rw [h]
    exact Subgroup.index_top

theorem plus_identity (s : ℕ) :
    (s + 1) ^ 3 * (((s + 1) ^ 2 - 1) * ((s + 1) ^ 3 - 1)) =
      (s + 1) ^ 3 * (s * (s + 2) * (s * (s ^ 2 + 3 * s + 3))) := by
  have h1 : (s + 1) ^ 2 - 1 = s * (s + 2) := by
    rw [show (s + 1) ^ 2 = s * (s + 2) + 1 by ring, Nat.add_sub_cancel]
  have h2 : (s + 1) ^ 3 - 1 = s * (s ^ 2 + 3 * s + 3) := by
    rw [show (s + 1) ^ 3 = s * (s ^ 2 + 3 * s + 3) + 1 by ring, Nat.add_sub_cancel]
  rw [h1, h2]

theorem minus_identity (s : ℕ) :
    (s + 1) ^ 3 * (((s + 1) ^ 2 - 1) * ((s + 1) ^ 3 + 1)) =
      (s + 1) ^ 3 * (s * (s + 2) * ((s + 2) * (s ^ 2 + s + 1))) := by
  have h1 : (s + 1) ^ 2 - 1 = s * (s + 2) := by
    rw [show (s + 1) ^ 2 = s * (s + 2) + 1 by ring, Nat.add_sub_cancel]
  have h2 : (s + 2) * (s ^ 2 + s + 1) = (s + 1) ^ 3 + 1 := by ring
  rw [h1, h2]




theorem L3Order_of_sl (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K] [CharP K p]
    (hmod : Nat.card K % 3 = 1) (n : ℕ)
    (hn : 3 * n = Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1))) :
    ∃ s, L3Order p s n := by
  obtain ⟨k, hk1, hkr⟩ := card_eq_pow_of_charP K p
  have hr2 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨s, hs⟩ : ∃ s, Nat.card K = s + 1 := ⟨Nat.card K - 1, by omega⟩
  refine ⟨s, ⟨k, hk1, hs.symm.trans hkr⟩, Or.inl ⟨by omega, by omega, ?_⟩⟩
  rw [hs] at hn
  rw [← plus_identity s]
  exact hn

theorem L3Order_of_su (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hq : p ^ j % 3 = 2)
    (hq2 : p ^ j ≠ 2)
    (hn : 3 * n = (p ^ j) ^ 3 * (((p ^ j) ^ 2 - 1) * ((p ^ j) ^ 3 + 1))) :
    ∃ s, L3Order p s n := by
  have hq1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨s, hs⟩ : ∃ s, p ^ j = s + 1 := ⟨p ^ j - 1, by omega⟩
  refine ⟨s, ⟨j, hj, hs.symm⟩, Or.inr ⟨by omega, by omega, ?_⟩⟩
  rw [hs] at hn
  rw [← minus_identity s]
  exact hn

theorem isL3Kind_finite (p : ℕ) (H : Type) [Group H] (hH : IsL3Kind p H) : Finite H := by
  rcases hH with hH1 | ⟨W, hWg, hW, ⟨e⟩⟩
  · rcases hH1 with ⟨K, hF, hfin, -, -, ⟨e⟩⟩ | ⟨K, hF, hfin, q, -, -, -, -, ⟨e⟩⟩
    · exact Finite.of_equiv _ e.toEquiv.symm
    · exact Finite.of_equiv _ e.toEquiv.symm
  · haveI : Finite W := by
      rcases hW with ⟨K, hF, hfin, -, -, ⟨f⟩⟩ | ⟨K, hF, hfin, q, -, -, -, -, ⟨f⟩⟩
      · exact Finite.of_equiv _ f.toEquiv.symm
      · exact Finite.of_equiv _ f.toEquiv.symm
    exact Finite.of_equiv _ e.toEquiv.symm

theorem isL3Kind_quot (p : ℕ) (hp : p.Prime) (H : Type) [Group H] [Finite H] (hH : IsL3Kind p H) :
    Nat.card (H ⧸ Subgroup.center H) = 1 ∨ ∃ s, L3Order p s (Nat.card (H ⧸ Subgroup.center H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hH with hH1 | ⟨W, hWg, hW, ⟨e⟩⟩
  · rcases hH1 with ⟨K, hF, hfin, hchar, hmod, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨e⟩⟩
    ·
      letI := hF
      haveI := hchar
      have h3 : 3 ∣ Nat.card K - 1 := by omega
      have hZ : Nat.card (Subgroup.center H) = 3 := by
        rw [card_center_transfer e, CFSG.Open.StatedCenterThree.card_center_statedSL_three h3]
      have hH' := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
      rw [hZ, Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three] at hH'
      refine Or.inr (L3Order_of_sl p K hmod _ ?_)
      rw [mul_comm 3]
      exact hH'.symm
    ·
      letI := hF
      haveI := hchar
      obtain ⟨k, hk1, hkr⟩ := card_eq_pow_of_charP K p
      have hqd : q ∣ p ^ k := by
        rw [← hkr, hcard]; exact dvd_pow_self q two_ne_zero
      obtain ⟨j, -, hqj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hqd
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; simp at hqj; omega
        · exact h0
      subst hqj
      have hK : Nat.card K = (p ^ j) ^ 2 := hcard
      have hquot := (su_quot_facts p j hj hq3 hq2 K hK H e).1
      refine Or.inr (L3Order_of_su p j hj _ hq3 hq2 ?_)
      rw [hquot]
      exact psu_card_three p j hj K hK hq3
  ·
    rcases hW with ⟨K, hF, hfin, hchar, hmod, ⟨f⟩⟩ | ⟨K, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨f⟩⟩
    · letI := hF
      haveI := hchar
      have h3 : 3 ∣ Nat.card K - 1 := by omega
      haveI : Finite W := Finite.of_equiv _ f.toEquiv.symm
      have hY := sl_quot_card K h3 f
      haveI : IsSimpleGroup (W ⧸ Subgroup.center W) := sl_quot_simple K f
      haveI : IsSimpleGroup H := e.isSimpleGroup
      rcases quot_center_cases H with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (L3Order_of_sl p K hmod _ ?_)
        have hHY : Nat.card H = Nat.card (W ⧸ Subgroup.center W) := Nat.card_congr e.toEquiv
        rw [h1, hHY, mul_comm 3]
        exact hY
    ·
      letI := hF
      haveI := hchar
      obtain ⟨k, hk1, hkr⟩ := card_eq_pow_of_charP K p
      have hqd : q ∣ p ^ k := by
        rw [← hkr, hcard]; exact dvd_pow_self q two_ne_zero
      obtain ⟨j, -, hqj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hqd
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0; simp at hqj; omega
        · exact h0
      subst hqj
      have hK : Nat.card K = (p ^ j) ^ 2 := hcard
      haveI : Finite W := Finite.of_equiv _ f.toEquiv.symm
      obtain ⟨hcardY, hsimpleY⟩ := su_quot_facts p j hj hq3 hq2 K hK W f
      haveI : IsSimpleGroup (W ⧸ Subgroup.center W) := hsimpleY
      haveI : IsSimpleGroup H := e.isSimpleGroup
      rcases quot_center_cases H with h1 | h1
      · exact Or.inl h1
      · refine Or.inr (L3Order_of_su p j hj _ hq3 hq2 ?_)
        have hHY : Nat.card H = Nat.card (W ⧸ Subgroup.center W) := Nat.card_congr e.toEquiv
        rw [h1, hHY, hcardY]
        exact psu_card_three p j hj K hK hq3


theorem one_ne_char_part {q v M : ℕ} (hq : q.Prime) (h : 1 = q ^ v * M)
    (hM : M < q ^ (2 * v)) : False := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp at h hM <;> omega
  · have h1 : q ∣ q ^ v * M := Dvd.dvd.mul_right (dvd_pow_self q hv.ne') M
    rw [← h] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)

theorem card_alt (n : ℕ) (hn : 2 ≤ n) : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem amb_small_contra {p n : ℕ}
    (hn : n = 60 ∨ n = 168 ∨ n = 360 ∨ n = 504 ∨ n = 6048 ∨ n = 25920)
    (hgroup : n = 1 ∨ ∃ s, L3Order p s n) : False := by
  rcases hgroup with h | ⟨s, hL⟩
  · omega
  · rcases L3Order.size hL with ⟨-, h⟩ | h <;> omega

theorem alt8_p_eq_two {p n : ℕ} (hp : p.Prime) (hn : n = 20160)
    (hgroup : n = 1 ∨ ∃ s, L3Order p s n) : p = 2 := by
  rcases hgroup with h | ⟨s, hL⟩
  · omega
  · rcases L3Order.size hL with ⟨hs, -⟩ | h
    · obtain ⟨⟨k, hk, hkp⟩, -⟩ := hL
      rw [hs] at hkp
      have h4 : p ∣ 4 := by
        have : p ∣ p ^ k := dvd_pow_self p (by omega)
        rw [← hkp] at this
        exact this
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h4)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    · omega

theorem amb_lie_order (q' : ℕ) (ld : TauCeti.LieTypeIndex) (hv : ld.Valid)
    (hi : CFSG.Yardstones.Md0ec50421ce4.ambiguousChev q' (TauCeti.CFSGIndex.lie ⟨ld, hv⟩)) :
    lieOrderFormula ld = 168 ∨ lieOrderFormula ld = 504 ∨ lieOrderFormula ld = 6048 ∨
      lieOrderFormula ld = 25920 := by
  cases ld with
  | A r q =>
    rcases r with _ | _ | r
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    · simp only [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      rcases hi with ⟨h7, -⟩ | ⟨h8, -⟩
      · left; simp only [lieOrderFormula]; rw [h7]; norm_num [orderA]
      · right; left; simp only [lieOrderFormula]; rw [h8]; norm_num [orderA]
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    · simp only [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      obtain ⟨h3, -⟩ := hi
      right; right; left
      simp only [lieOrderFormula]; rw [h3]; decide
    · simp only [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      obtain ⟨h2, -⟩ := hi
      right; right; right
      simp only [lieOrderFormula]; rw [h2]; decide
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
  | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

theorem l3CharUnique_of_bridge (hb : LieOrderBridge) :
    ∀ (p q' : ℕ) (H : Type) [Group H], p.Prime → IsL3Kind p H →
      CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q' (H ⧸ Subgroup.center H) → q' = p := by
  intro p q' H _ hp hH hchev
  haveI : Finite H := isL3Kind_finite p H hH
  haveI : Finite (H ⧸ Subgroup.center H) := inferInstance
  have hgroup := isL3Kind_quot p hp H hH
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  ·
    cases i with
    | cyclic _ _ => simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
    | alternating _ _ => simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
    | sporadic _ => simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
    | lie d =>
      simp only [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
      have hn := hb d _ ⟨e⟩
      obtain ⟨v, M, hv, hM⟩ := lie_char_part d.1 d.2
      have hq' : q'.Prime := by
        rw [← hi]; exact TauCeti.LieTypeIndex.characteristic_prime d.1
      rw [hi] at hv hM
      have key : Nat.card (H ⧸ Subgroup.center H) = q' ^ v * M := hn.trans hv
      have hdvd : q' ^ v ∣ Nat.card (H ⧸ Subgroup.center H) := by
        rw [key]; exact dvd_mul_right _ _
      have hlt : Nat.card (H ⧸ Subgroup.center H) < q' ^ (3 * v) := by
        rw [key]
        calc q' ^ v * M < q' ^ v * q' ^ (2 * v) :=
              Nat.mul_lt_mul_of_pos_left hM (pow_pos hq'.pos _)
          _ = q' ^ (3 * v) := by ring
      rcases hgroup with h1 | ⟨s, hL⟩
      · exact (one_ne_char_part hq' (h1.symm.trans key) hM).elim
      · by_contra hne
        exact absurd hlt (not_lt.2 (qpow_bound hq' hp hne hL hdvd))
  ·
    cases i with
    | cyclic _ _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    | alternating n hn5 =>
      simp only [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      have hcard : Nat.card (H ⧸ Subgroup.center H) = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans (card_alt n (by omega))
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hq2⟩
      · exact (amb_small_contra (by rw [hcard]; norm_num [Nat.factorial]) hgroup).elim
      · exact (amb_small_contra (by rw [hcard]; norm_num [Nat.factorial]) hgroup).elim
      · have hpt := alt8_p_eq_two hp (by rw [hcard]; norm_num [Nat.factorial]) hgroup
        rw [hq2, hpt]
    | lie d =>
      obtain ⟨ld, hvld⟩ := d
      have hn := hb ⟨ld, hvld⟩ _ ⟨e⟩
      have hval := amb_lie_order q' ld hvld hi
      exact (amb_small_contra (by
        rw [hn]
        rcases hval with h | h | h | h <;> simp [h]) hgroup).elim
    | sporadic _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

theorem l3CharUnique_holds :
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.L3CharUnique :=
  l3CharUnique_of_bridge lieOrderBridge_holds

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

end
