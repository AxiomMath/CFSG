module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S3.L3Ord

open CFSG.Open (ordA ordTwistedA ordRee ordTrialityD4)

theorem lower_R {q : ℕ} (hq : 2 ≤ q) :
    q ^ 6 * (q ^ 2 - 2) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : 8 ≤ q ^ 3 := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 2 := ⟨q ^ 2 - 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, q ^ 3 = b + 1 := ⟨q ^ 3 - 1, by omega⟩
  have e1 : q ^ 2 - 1 = a + 1 := by omega
  have e2 : q ^ 3 - 1 = b := by omega
  have e3 : q ^ 2 - 2 = a := by omega
  rw [e1, e2, e3]
  have : q ^ 6 = (q ^ 3) ^ 2 := by ring
  rw [this, hb]
  have hab : a ≤ b := by
    have : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  nlinarith [Nat.zero_le a, Nat.zero_le b]

theorem gen2 {c q : ℕ} (hq : c + 2 ≤ q) : c * q ^ 3 < (q ^ 2 - 2) ^ 2 := by
  have hq2 : 2 ≤ q := by omega
  have h2 : 2 ≤ q ^ 2 := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 2 := ⟨q ^ 2 - 2, by omega⟩
  have e : q ^ 2 - 2 = a := by omega
  rw [e]
  have h4 : q ^ 4 = (a + 2) ^ 2 := by rw [← ha]; ring
  have h5 : (c + 2) * q ^ 3 ≤ q ^ 4 := by
    calc (c + 2) * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ hq
      _ = q ^ 4 := by ring
  have h6 : 4 * q ^ 2 ≤ 2 * q ^ 3 := by nlinarith
  nlinarith

theorem gen5 {c t0 t : ℕ} (ht : t0 ≤ t) (hc : c * (t0 + 2) ^ 3 < t0 ^ 5) :
    c * (t + 2) ^ 3 < t ^ 5 := by
  have ht0 : 0 < t0 := by
    rcases Nat.eq_zero_or_pos t0 with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have h1 : t0 * (t + 2) ≤ (t0 + 2) * t := by nlinarith
  have h2 : t0 ^ 3 * (t + 2) ^ 3 ≤ (t0 + 2) ^ 3 * t ^ 3 := by
    calc t0 ^ 3 * (t + 2) ^ 3 = (t0 * (t + 2)) ^ 3 := by ring
      _ ≤ ((t0 + 2) * t) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = (t0 + 2) ^ 3 * t ^ 3 := by ring
  have h3 : t0 ^ 2 * t ^ 3 ≤ t ^ 5 := by
    calc t0 ^ 2 * t ^ 3 ≤ t ^ 2 * t ^ 3 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ht 2)
      _ = t ^ 5 := by ring
  have htpos : 0 < t ^ 3 := pow_pos (lt_of_lt_of_le ht0 ht) 3
  have h4 : t0 ^ 3 * (c * (t + 2) ^ 3) < t0 ^ 3 * t ^ 5 := by
    calc t0 ^ 3 * (c * (t + 2) ^ 3) = c * (t0 ^ 3 * (t + 2) ^ 3) := by ring
      _ ≤ c * ((t0 + 2) ^ 3 * t ^ 3) := Nat.mul_le_mul_left _ h2
      _ = (c * (t0 + 2) ^ 3) * t ^ 3 := by ring
      _ < t0 ^ 5 * t ^ 3 := Nat.mul_lt_mul_of_pos_right hc htpos
      _ = t0 ^ 3 * (t0 ^ 2 * t ^ 3) := by ring
      _ ≤ t0 ^ 3 * t ^ 5 := Nat.mul_le_mul_left _ h3
  exact Nat.lt_of_mul_lt_mul_left h4

theorem ordA_three_le (q : ℕ) : ordA 3 q ≤ q ^ 15 := by
  unfold ordA
  have e : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
  rw [show 3 * (3 + 1) / 2 = 6 from rfl, e]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  calc q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) / Nat.gcd (3 + 1) (q - 1)
      ≤ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := Nat.div_le_self _ _
    _ ≤ q ^ 6 * (q ^ 2 * (q ^ 3 * q ^ 4)) := by gcongr <;> omega
    _ = q ^ 15 := by ring

theorem ordA_four_le (q : ℕ) : ordA 4 q ≤ q ^ 24 := by
  unfold ordA
  have e : Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} := by decide
  rw [show 4 * (4 + 1) / 2 = 10 from rfl, e]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  calc q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) / Nat.gcd (4 + 1) (q - 1)
      ≤ q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) :=
        Nat.div_le_self _ _
    _ ≤ q ^ 10 * (q ^ 2 * (q ^ 3 * (q ^ 4 * q ^ 5))) := by gcongr <;> omega
    _ = q ^ 24 := by ring

private theorem toNat_sub_one_pow (q i : ℕ) (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  have h1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have : ((q : ℤ) ^ i - (-1 : ℤ) ^ i) = ((q ^ i - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1]
    rw [hi.neg_one_pow]
  rw [this]
  exact Int.toNat_natCast _

private theorem toNat_add_one_pow (q i : ℕ) (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  have : ((q : ℤ) ^ i - (-1 : ℤ) ^ i) = ((q ^ i + 1 : ℕ) : ℤ) := by
    push_cast
    rw [hi.neg_one_pow]
    ring
  rw [this]
  exact Int.toNat_natCast _

theorem ordTwistedA_three_le {q : ℕ} (hq : 1 ≤ q) : ordTwistedA 3 q ≤ 2 * q ^ 15 := by
  unfold ordTwistedA
  have e : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
  rw [show 3 * (3 + 1) / 2 = 6 from rfl, e]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    toNat_sub_one_pow q 2 hq (by decide), toNat_add_one_pow q 3 (by decide),
    toNat_sub_one_pow q 4 hq (by decide)]
  have h3 : q ^ 3 + 1 ≤ 2 * q ^ 3 := by
    have := Nat.one_le_pow 3 q hq
    omega
  calc q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / Nat.gcd (3 + 1) (q + 1)
      ≤ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) := Nat.div_le_self _ _
    _ ≤ q ^ 6 * (q ^ 2 * ((2 * q ^ 3) * q ^ 4)) := by
        gcongr
        all_goals omega
    _ = 2 * q ^ 15 := by ring

theorem ordTwistedA_four_le {q : ℕ} (hq : 1 ≤ q) : ordTwistedA 4 q ≤ 4 * q ^ 24 := by
  unfold ordTwistedA
  have e : Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} := by decide
  rw [show 4 * (4 + 1) / 2 = 10 from rfl, e]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, toNat_sub_one_pow q 2 hq (by decide), toNat_add_one_pow q 3 (by decide),
    toNat_sub_one_pow q 4 hq (by decide), toNat_add_one_pow q 5 (by decide)]
  have h3 : q ^ 3 + 1 ≤ 2 * q ^ 3 := by
    have := Nat.one_le_pow 3 q hq
    omega
  have h5 : q ^ 5 + 1 ≤ 2 * q ^ 5 := by
    have := Nat.one_le_pow 5 q hq
    omega
  calc q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) / Nat.gcd (4 + 1) (q + 1)
      ≤ q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) :=
        Nat.div_le_self _ _
    _ ≤ q ^ 10 * (q ^ 2 * ((2 * q ^ 3) * (q ^ 4 * (2 * q ^ 5)))) := by
        gcongr
        all_goals omega
    _ = 4 * q ^ 24 := by ring

theorem ordTrialityD4_le {q : ℕ} (hq : 2 ≤ q) : ordTrialityD4 q ≤ 2 * q ^ 28 := by
  unfold ordTrialityD4
  have h4 : q ^ 4 + 1 ≤ q ^ 8 := by
    have h1 : 16 ≤ q ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have : q ^ 8 = q ^ 4 * q ^ 4 := by ring
    nlinarith
  have h8 : q ^ 8 + q ^ 4 + 1 ≤ 2 * q ^ 8 := by omega
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * (2 * q ^ 8) * q ^ 6 * q ^ 2 := by
        gcongr
        all_goals omega
    _ = 2 * q ^ 28 := by ring

theorem ordRee_le {q : ℕ} (hq : 1 ≤ q) : ordRee q ≤ 2 * q ^ 7 := by
  unfold ordRee
  have h3 : q ^ 3 + 1 ≤ 2 * q ^ 3 := by
    have := Nat.one_le_pow 3 q hq
    omega
  calc q ^ 3 * (q ^ 3 + 1) * (q - 1) ≤ q ^ 3 * (2 * q ^ 3) * q := by
        gcongr
        all_goals omega
    _ = 2 * q ^ 7 := by ring

theorem size_L4 {q q' : ℕ} (hq : 5 ≤ q) (hq' : 2 ≤ q') (h : q' ^ 6 ≤ q ^ 3) :
    3 * ordA 3 q' < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  by_cases hbig : 11 ≤ q
  · have hA := ordA_three_le q'
    have hR := lower_R (by omega : 2 ≤ q)
    have h1 : (3 * ordA 3 q') ^ 2 ≤ 9 * q ^ 15 := by
      calc (3 * ordA 3 q') ^ 2 = 9 * (ordA 3 q') ^ 2 := by ring
        _ ≤ 9 * (q' ^ 15) ^ 2 := by gcongr
        _ = 9 * (q' ^ 6) ^ 5 := by ring
        _ ≤ 9 * (q ^ 3) ^ 5 := by gcongr
        _ = 9 * q ^ 15 := by ring
    have h2 : 9 * q ^ 15 < (q ^ 6 * (q ^ 2 - 2)) ^ 2 := by
      have := gen2 (c := 9) (q := q) (by omega)
      calc 9 * q ^ 15 = q ^ 12 * (9 * q ^ 3) := by ring
        _ < q ^ 12 * (q ^ 2 - 2) ^ 2 := Nat.mul_lt_mul_of_pos_left this (by positivity)
        _ = (q ^ 6 * (q ^ 2 - 2)) ^ 2 := by ring
    have h3 : (3 * ordA 3 q') ^ 2 < (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ^ 2 :=
      lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (Nat.pow_le_pow_left hR 2))
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
  · have hq10 : q ≤ 10 := by omega
    have hq3 : q' ≤ 3 := by
      by_contra hc
      have h1 : 4 ^ 6 ≤ q' ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have h2 : q ^ 3 ≤ 10 ^ 3 := Nat.pow_le_pow_left hq10 3
      omega
    interval_cases q <;> interval_cases q' <;> revert h <;> decide

theorem size_U4 {q q' : ℕ} (hq : 5 ≤ q) (hq' : 2 ≤ q') (h : q' ^ 6 ≤ q ^ 3) :
    3 * ordTwistedA 3 q' < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  by_cases hbig : 38 ≤ q
  · have hA := ordTwistedA_three_le (by omega : 1 ≤ q')
    have hR := lower_R (by omega : 2 ≤ q)
    have h1 : (3 * ordTwistedA 3 q') ^ 2 ≤ 36 * q ^ 15 := by
      calc (3 * ordTwistedA 3 q') ^ 2 = 9 * (ordTwistedA 3 q') ^ 2 := by ring
        _ ≤ 9 * (2 * q' ^ 15) ^ 2 := by gcongr
        _ = 36 * (q' ^ 6) ^ 5 := by ring
        _ ≤ 36 * (q ^ 3) ^ 5 := by gcongr
        _ = 36 * q ^ 15 := by ring
    have h2 : 36 * q ^ 15 < (q ^ 6 * (q ^ 2 - 2)) ^ 2 := by
      have := gen2 (c := 36) (q := q) (by omega)
      calc 36 * q ^ 15 = q ^ 12 * (36 * q ^ 3) := by ring
        _ < q ^ 12 * (q ^ 2 - 2) ^ 2 := Nat.mul_lt_mul_of_pos_left this (by positivity)
        _ = (q ^ 6 * (q ^ 2 - 2)) ^ 2 := by ring
    have h3 : (3 * ordTwistedA 3 q') ^ 2 < (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ^ 2 :=
      lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (Nat.pow_le_pow_left hR 2))
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
  · have hq37 : q ≤ 37 := by omega
    have hq6 : q' ≤ 6 := by
      by_contra hc
      have h1 : 7 ^ 6 ≤ q' ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have h2 : q ^ 3 ≤ 37 ^ 3 := Nat.pow_le_pow_left hq37 3
      omega
    interval_cases q <;> interval_cases q' <;> revert h <;> decide

theorem size_L5 {q q' : ℕ} (hq : 5 ≤ q) (hq' : 2 ≤ q') (h : q' ^ 10 ≤ q ^ 3) :
    3 * ordA 4 q' < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have hA := ordA_four_le q'
  have hR := lower_R (by omega : 2 ≤ q)
  have h1 : (3 * ordA 4 q') ^ 5 ≤ 243 * q ^ 36 := by
    calc (3 * ordA 4 q') ^ 5 = 243 * (ordA 4 q') ^ 5 := by ring
      _ ≤ 243 * (q' ^ 24) ^ 5 := by gcongr
      _ = 243 * (q' ^ 10) ^ 12 := by ring
      _ ≤ 243 * (q ^ 3) ^ 12 := by gcongr
      _ = 243 * q ^ 36 := by ring
  have h2 : 243 * q ^ 36 < (q ^ 6 * (q ^ 2 - 2)) ^ 5 := by
    have ht : 23 ≤ q ^ 2 - 2 := by
      have : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have := gen5 (c := 243) (t0 := 23) (t := q ^ 2 - 2) ht (by norm_num)
    have e : q ^ 2 - 2 + 2 = q ^ 2 := by
      have : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    rw [e] at this
    calc 243 * q ^ 36 = q ^ 30 * (243 * (q ^ 2) ^ 3) := by ring
      _ < q ^ 30 * (q ^ 2 - 2) ^ 5 := Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ = (q ^ 6 * (q ^ 2 - 2)) ^ 5 := by ring
  have h3 : (3 * ordA 4 q') ^ 5 < (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ^ 5 :=
    lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (Nat.pow_le_pow_left hR 5))
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3

theorem size_U5 {q q' : ℕ} (hq : 5 ≤ q) (hq' : 2 ≤ q') (h : q' ^ 10 ≤ q ^ 3) :
    3 * ordTwistedA 4 q' < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  by_cases hbig : 25 ≤ q
  · have hA := ordTwistedA_four_le (by omega : 1 ≤ q')
    have hR := lower_R (by omega : 2 ≤ q)
    have h1 : (3 * ordTwistedA 4 q') ^ 5 ≤ 248832 * q ^ 36 := by
      calc (3 * ordTwistedA 4 q') ^ 5 = 243 * (ordTwistedA 4 q') ^ 5 := by ring
        _ ≤ 243 * (4 * q' ^ 24) ^ 5 := by gcongr
        _ = 248832 * (q' ^ 10) ^ 12 := by ring
        _ ≤ 248832 * (q ^ 3) ^ 12 := by gcongr
        _ = 248832 * q ^ 36 := by ring
    have h2 : 248832 * q ^ 36 < (q ^ 6 * (q ^ 2 - 2)) ^ 5 := by
      have ht : 623 ≤ q ^ 2 - 2 := by
        have : 25 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hbig 2
        omega
      have := gen5 (c := 248832) (t0 := 623) (t := q ^ 2 - 2) ht (by norm_num)
      have e : q ^ 2 - 2 + 2 = q ^ 2 := by
        have : 25 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hbig 2
        omega
      rw [e] at this
      calc 248832 * q ^ 36 = q ^ 30 * (248832 * (q ^ 2) ^ 3) := by ring
        _ < q ^ 30 * (q ^ 2 - 2) ^ 5 := Nat.mul_lt_mul_of_pos_left this (by positivity)
        _ = (q ^ 6 * (q ^ 2 - 2)) ^ 5 := by ring
    have h3 : (3 * ordTwistedA 4 q') ^ 5 < (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ^ 5 :=
      lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (Nat.pow_le_pow_left hR 5))
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
  · have hq24 : q ≤ 24 := by omega
    have hq2 : q' ≤ 2 := by
      by_contra hc
      have h1 : 3 ^ 10 ≤ q' ^ 10 := Nat.pow_le_pow_left (by omega) 10
      have h2 : q ^ 3 ≤ 24 ^ 3 := Nat.pow_le_pow_left hq24 3
      omega
    interval_cases q <;> interval_cases q' <;> revert h <;> decide

theorem size_3D4 {q q' : ℕ} (hq : 5 ≤ q) (hq' : 2 ≤ q') (h : q' ^ 12 ≤ q ^ 3) :
    3 * ordTrialityD4 q' < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  by_cases hbig : 7 ≤ q
  · have hA := ordTrialityD4_le hq'
    have hR := lower_R (by omega : 2 ≤ q)
    have h1 : (3 * ordTrialityD4 q') ^ 3 ≤ 216 * q ^ 21 := by
      calc (3 * ordTrialityD4 q') ^ 3 = 27 * (ordTrialityD4 q') ^ 3 := by ring
        _ ≤ 27 * (2 * q' ^ 28) ^ 3 := by gcongr
        _ = 216 * (q' ^ 12) ^ 7 := by ring
        _ ≤ 216 * (q ^ 3) ^ 7 := by gcongr
        _ = 216 * q ^ 21 := by ring
    have h2 : 216 * q ^ 21 < (q ^ 6 * (q ^ 2 - 2)) ^ 3 := by
      have h6 : 6 * q < q ^ 2 - 2 := by
        have : 7 * q ≤ q ^ 2 := by nlinarith
        omega
      have := Nat.pow_lt_pow_left h6 (by norm_num : (3 : ℕ) ≠ 0)
      calc 216 * q ^ 21 = q ^ 18 * (6 * q) ^ 3 := by ring
        _ < q ^ 18 * (q ^ 2 - 2) ^ 3 := Nat.mul_lt_mul_of_pos_left this (by positivity)
        _ = (q ^ 6 * (q ^ 2 - 2)) ^ 3 := by ring
    have h3 : (3 * ordTrialityD4 q') ^ 3 < (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ^ 3 :=
      lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (Nat.pow_le_pow_left hR 3))
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3
  · exfalso
    have hq6 : q ≤ 6 := by omega
    have h1 : 2 ^ 12 ≤ q' ^ 12 := Nat.pow_le_pow_left hq' 12
    have h2 : q ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left hq6 3
    omega

theorem size_Ree {q q' : ℕ} (hq : 5 ≤ q) (hq' : 2 ≤ q') (h : q' ^ 3 ≤ q ^ 3) :
    3 * ordRee q' < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have hqq : q' ≤ q := (Nat.pow_le_pow_iff_left (by norm_num)).1 h
  by_cases hbig : 7 ≤ q
  · have hA := ordRee_le (by omega : 1 ≤ q')
    have hR := lower_R (by omega : 2 ≤ q)
    have h7 : q' ^ 7 ≤ q ^ 7 := Nat.pow_le_pow_left hqq 7
    have h6 : 6 * q < q ^ 2 - 2 := by
      have : 7 * q ≤ q ^ 2 := by nlinarith
      omega
    calc 3 * ordRee q' ≤ 3 * (2 * q' ^ 7) := by gcongr
      _ ≤ 6 * q ^ 7 := by omega
      _ = q ^ 6 * (6 * q) := by ring
      _ < q ^ 6 * (q ^ 2 - 2) := Nat.mul_lt_mul_of_pos_left h6 (by positivity)
      _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := hR
  · have hq6 : q ≤ 6 := by omega
    interval_cases q <;> interval_cases q' <;> revert h <;> decide

end CFSG.GH74.Generic.S3.L3Ord
