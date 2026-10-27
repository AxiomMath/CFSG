module

public import CFSG.GH74.Generic.JMaxShapes
public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.GH74.Generic.S3.L3Ord

open CFSG.Open

theorem ordA_two (q : ℕ) : ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold ordA
  rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
    Finset.prod_pair (by norm_num)]

theorem ordTwistedA_two (q : ℕ) :
    ordTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  unfold ordTwistedA
  rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
    Finset.prod_pair (by norm_num)]
  have h2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) ∨ q = 0 := by
      rcases Nat.eq_zero_or_pos q with h | h
      · exact Or.inr h
      · left
        have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h
        push_cast [Nat.cast_sub this]
        ring
    rcases this with h | h
    · rw [h]; exact Int.toNat_natCast _
    · subst h; simp
  have h3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this]; exact Int.toNat_natCast _
  rw [h2, h3]


theorem ordA_one (q : ℕ) : ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, pow_one]

theorem two_mul_ordA_one {q : ℕ} (hq : Odd q) : 2 * ordA 1 q = q * (q ^ 2 - 1) := by
  obtain ⟨m, rfl⟩ := hq
  have hg : Nat.gcd 2 (2 * m + 1 - 1) = 2 := by
    rw [show 2 * m + 1 - 1 = 2 * m by omega]
    exact Nat.gcd_eq_left (Dvd.intro _ rfl)
  rw [ordA_one, hg]
  have hsq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    rw [show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]; simp
  rw [hsq, show (2 * m + 1) * (4 * (m * (m + 1))) = 2 * ((2 * m + 1) * (2 * (m * (m + 1)))) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]

theorem ordA_two_mul (q : ℕ) (hq : 1 ≤ q) :
    ordA 2 q * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  rw [ordA_two]
  apply Nat.div_mul_cancel
  have h1 : Nat.gcd 3 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
  have h2 : q - 1 ∣ q ^ 2 - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    refine ⟨m + 2, ?_⟩
    rw [Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring]; simp
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (h1.trans h2) _) _

theorem ordTwistedA_two_mul (q : ℕ) :
    ordTwistedA 2 q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  rw [ordTwistedA_two]
  apply Nat.div_mul_cancel
  have h1 : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
  have h2 : q + 1 ∣ q ^ 2 - 1 := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp
    · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      refine ⟨m, ?_⟩
      rw [show (m + 1) ^ 2 = m * (m + 2) + 1 by ring]; simp [mul_comm]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (h1.trans h2) _) _


theorem le_ordA_two {q : ℕ} (hq : 5 ≤ q) : 124000 ≤ ordA 2 q := by
  have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hg0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h := ordA_two_mul q (by omega)
  have h3 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 24 ≤ q ^ 2 - 1 := by
    have : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have h4 : 124 ≤ q ^ 3 - 1 := by omega
  have h5 : 372000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    calc 372000 = 125 * (24 * 124) := by norm_num
      _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h4)
  by_contra hlt
  have hlt := not_le.mp hlt
  have : ordA 2 q * Nat.gcd 3 (q - 1) < 124000 * 3 := by
    calc ordA 2 q * Nat.gcd 3 (q - 1) ≤ ordA 2 q * 3 := Nat.mul_le_mul_left _ hg
      _ < 124000 * 3 := by omega
  omega

theorem le_ordTwistedA_two {q : ℕ} (hq : 5 ≤ q) : 124000 ≤ ordTwistedA 2 q := by
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have h := ordTwistedA_two_mul q
  have h3 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 24 ≤ q ^ 2 - 1 := by
    have : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have h4 : 126 ≤ q ^ 3 + 1 := by omega
  have h5 : 378000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    calc 378000 = 125 * (24 * 126) := by norm_num
      _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h4)
  by_contra hlt
  have hlt := not_le.mp hlt
  have : ordTwistedA 2 q * Nat.gcd 3 (q + 1) < 124000 * 3 := by
    calc ordTwistedA 2 q * Nat.gcd 3 (q + 1) ≤ ordTwistedA 2 q * 3 := Nat.mul_le_mul_left _ hg
      _ < 124000 * 3 := by omega
  omega


theorem ordA_two_le {q : ℕ} (hq : 1 ≤ q) : ordA 2 q ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h := ordA_two_mul q hq
  have hg0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h1 : ordA 2 q ≤ ordA 2 q * Nat.gcd 3 (q - 1) := Nat.le_mul_of_pos_right _ hg0
  have h2 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  omega

theorem ordTwistedA_two_le (q : ℕ) :
    ordTwistedA 2 q ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h := ordTwistedA_two_mul q
  have hg0 : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h1 : ordTwistedA 2 q ≤ ordTwistedA 2 q * Nat.gcd 3 (q + 1) := Nat.le_mul_of_pos_right _ hg0
  omega

theorem prime_pow_dvd_ordA_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    p ^ (3 * f) ∣ ordA 2 (p ^ f) := by
  have h := ordA_two_mul (p ^ f) (Nat.one_le_pow _ _ hp.pos)
  have hcop : Nat.Coprime (p ^ (3 * f)) (Nat.gcd 3 (p ^ f - 1)) := by
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have h3 : p ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    subst hp3
    have h1 : 3 ∣ 3 ^ f - 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h2 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have : 0 < 3 ^ f := by positivity
    omega
  have hdvd : p ^ (3 * f) ∣ ordA 2 (p ^ f) * Nat.gcd 3 (p ^ f - 1) := by
    rw [h, pow_mul', ← pow_mul]
    exact Dvd.intro _ rfl
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem prime_pow_dvd_ordTwistedA_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    p ^ (3 * f) ∣ ordTwistedA 2 (p ^ f) := by
  have h := ordTwistedA_two_mul (p ^ f)
  have hcop : Nat.Coprime (p ^ (3 * f)) (Nat.gcd 3 (p ^ f + 1)) := by
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have h3 : p ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    subst hp3
    have h1 : 3 ∣ 3 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h2 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  have hdvd : p ^ (3 * f) ∣ ordTwistedA 2 (p ^ f) * Nat.gcd 3 (p ^ f + 1) := by
    rw [h, pow_mul', ← pow_mul]
    exact Dvd.intro _ rfl
  exact hcop.dvd_of_dvd_mul_right hdvd


theorem pow_dvd_trichotomy {p k q' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : 1 ≤ q')
    (h : p ^ k ∣ q' * ((q' - 1) * (q' + 1))) :
    p ^ k ∣ q' ∨ p ^ k ∣ q' - 1 ∨ p ^ k ∣ q' + 1 := by
  by_cases hpq : p ∣ q'
  · left
    have hn1 : ¬ p ∣ q' - 1 := fun hd => by
      have : p ∣ q' - (q' - 1) := Nat.dvd_sub hpq hd
      rw [show q' - (q' - 1) = 1 by omega] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    have hn2 : ¬ p ∣ q' + 1 := fun hd => by
      have : p ∣ q' + 1 - q' := Nat.dvd_sub hd hpq
      rw [show q' + 1 - q' = 1 by omega] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    have hcop : Nat.Coprime (p ^ k) ((q' - 1) * (q' + 1)) := by
      apply Nat.Coprime.pow_left
      rw [hp.coprime_iff_not_dvd]
      intro hd
      rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
      · exact hn1 h1
      · exact hn2 h1
    exact hcop.dvd_of_dvd_mul_right h
  · have hcop : Nat.Coprime (p ^ k) q' := by
      apply Nat.Coprime.pow_left
      rw [hp.coprime_iff_not_dvd]
      exact hpq
    have h' : p ^ k ∣ (q' - 1) * (q' + 1) := hcop.dvd_of_dvd_mul_left h
    by_cases hp1 : p ∣ q' - 1
    · right; left
      have hn2 : ¬ p ∣ q' + 1 := fun hd => by
        have : p ∣ q' + 1 - (q' - 1) := Nat.dvd_sub hd hp1
        rw [show q' + 1 - (q' - 1) = 2 by omega] at this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
      have hcop2 : Nat.Coprime (p ^ k) (q' + 1) := by
        apply Nat.Coprime.pow_left
        rw [hp.coprime_iff_not_dvd]
        exact hn2
      exact hcop2.dvd_of_dvd_mul_right h'
    · right; right
      have hcop2 : Nat.Coprime (p ^ k) (q' - 1) := by
        apply Nat.Coprime.pow_left
        rw [hp.coprime_iff_not_dvd]
        exact hp1
      exact hcop2.dvd_of_dvd_mul_left h'

theorem size_contra {x A B N : ℤ} (hA : 125 ≤ A) (hB : 5 * B ≤ A) (hx : A ≤ x + 1)
    (hN : 2 * N = x * (x ^ 2 - 1)) (hNle : N ≤ A * ((B - 1) * (A + 1))) : False := by
  have hx1 : A - 1 ≤ x := by linarith
  have h1 : (0 : ℤ) ≤ x ^ 2 + x * (A - 1) + (A - 1) ^ 2 - 1 := by nlinarith
  have key : (A - 1) * ((A - 1) ^ 2 - 1) ≤ x * (x ^ 2 - 1) := by
    have e : x * (x ^ 2 - 1) - (A - 1) * ((A - 1) ^ 2 - 1) =
        (x - (A - 1)) * (x ^ 2 + x * (A - 1) + (A - 1) ^ 2 - 1) := by ring
    have : 0 ≤ (x - (A - 1)) * (x ^ 2 + x * (A - 1) + (A - 1) ^ 2 - 1) :=
      mul_nonneg (by linarith) h1
    linarith
  have h2 : A * ((A - 1) * (A - 2)) ≤ 2 * (A * ((B - 1) * (A + 1))) := by nlinarith
  have hApos : (0 : ℤ) < A := by linarith
  have h3 : (A - 1) * (A - 2) ≤ 2 * ((B - 1) * (A + 1)) := by
    have : A * ((A - 1) * (A - 2)) ≤ A * (2 * ((B - 1) * (A + 1))) := by linarith
    exact le_of_mul_le_mul_left this hApos
  nlinarith

theorem ordA_one_ne {p f q' N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hN : N ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1))) (hN0 : 0 < N)
    (hdvd : p ^ (3 * f) ∣ N) (hq' : Odd q') : ordA 1 q' ≠ N := by
  intro hEq
  have h2N : 2 * N = q' * (q' ^ 2 - 1) := by rw [← hEq]; exact two_mul_ordA_one hq'
  have hq1 : 1 ≤ q' := hq'.pos
  have hsq : q' ^ 2 - 1 = (q' - 1) * (q' + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q' = m + 1 := ⟨q' - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (m + 1) ^ 2 = m * (m + 2) + 1 by ring]; simp
  have hdvd2 : p ^ (3 * f) ∣ q' * ((q' - 1) * (q' + 1)) := by
    rw [← hsq, ← h2N]
    exact Dvd.dvd.mul_left hdvd 2
  have hq3 : 3 ≤ q' := by
    by_contra hlt
    have : q' ≤ 2 := by omega
    interval_cases q'
    · simp at h2N; omega
    · exact absurd hq' (by decide)
  have hle : (p ^ f) ^ 3 ≤ q' + 1 := by
    have hpow : p ^ (3 * f) = (p ^ f) ^ 3 := by rw [pow_mul']
    rw [← hpow]
    rcases pow_dvd_trichotomy hp hp2 hq1 hdvd2 with h | h | h
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
    · exact Nat.le_of_dvd (by omega) h
  have hq5 : 5 ≤ p ^ f := hq
  apply size_contra (x := (q' : ℤ)) (A := ((p ^ f) ^ 3 : ℕ)) (B := (((p ^ f) ^ 2 : ℕ) : ℤ))
    (N := (N : ℤ))
  · have : 5 ^ 3 ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq5 3
    exact_mod_cast (by omega : 125 ≤ (p ^ f) ^ 3)
  · have : 5 * (p ^ f) ^ 2 ≤ (p ^ f) ^ 3 := by
      calc 5 * (p ^ f) ^ 2 ≤ (p ^ f) * (p ^ f) ^ 2 := Nat.mul_le_mul_right _ hq5
        _ = (p ^ f) ^ 3 := by ring
    exact_mod_cast this
  · exact_mod_cast hle
  · have : (2 : ℤ) * N = (q' : ℤ) * ((q' : ℤ) ^ 2 - 1) := by
      have h1 : 1 ≤ q' ^ 2 := Nat.one_le_pow _ _ (by omega)
      have := congrArg (fun n : ℕ => (n : ℤ)) h2N
      push_cast [Nat.cast_sub h1] at this
      exact this
    exact this
  · have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e : (((p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) : ℕ) : ℤ) =
        (((p ^ f) ^ 3 : ℕ) : ℤ) *
          (((((p ^ f) ^ 2 : ℕ) : ℤ) - 1) * ((((p ^ f) ^ 3 : ℕ) : ℤ) + 1)) := by
      push_cast [Nat.cast_sub h1]; ring
    calc (N : ℤ) ≤ (((p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) : ℕ) : ℤ) := by
          exact_mod_cast hN
      _ = _ := e


end CFSG.GH74.Generic.S3.L3Ord

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.E2 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.S3.L3Ord

section Groups

variable {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}

theorem l3_card_bounds (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h : LieModel X t 3 p f) :
    124000 ≤ Nat.card X ∧ Nat.card X ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) ∧
      p ^ (3 * f) ∣ Nat.card X := by
  have hf : 1 ≤ f := by
    by_contra h0
    have : f = 0 := by omega
    subst this
    simp at hq
  rcases ht with rfl | rfl
  · have hc := card_of_lieModel_PSL (n := 3) (by norm_num) h
    simp only [show 3 - 1 = 2 from rfl] at hc
    rw [hc]
    exact ⟨le_ordA_two hq, ordA_two_le (by omega), prime_pow_dvd_ordA_two hp hf⟩
  · have hc := card_of_lieModel_PSU (n := 3) (by norm_num) hp2 h
    simp only [show 3 - 1 = 2 from rfl] at hc
    rw [hc]
    exact ⟨le_ordTwistedA_two hq, ordTwistedA_two_le _, prime_pow_dvd_ordTwistedA_two hp hf⟩

theorem l3_ne_L2 (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h : LieModel X t 3 p f) {p' f' : ℕ} (hp' : p'.Prime) (hp'2 : p' ≠ 2)
    (h' : LieModel X .PSL 2 p' f') : False := by
  obtain ⟨h1, h2, h3⟩ := l3_card_bounds ht hp hp2 hq h
  have hc := card_of_lieModel_PSL (n := 2) (by norm_num) h'
  simp only [show 2 - 1 = 1 from rfl] at hc
  have hodd : Odd (p' ^ f') := (hp'.odd_of_ne_two hp'2).pow
  exact ordA_one_ne hp hp2 hq h2 (by omega) h3 hodd hc.symm

theorem l3_not_inT2 (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h : LieModel X t 3 p f) : ¬ InT2 X := by
  intro hT
  have hmod : LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f := by
    rcases ht with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have hcen : center X = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hT.1 hmod
  obtain ⟨h1, -, -⟩ := l3_card_bounds ht hp hp2 hq h
  rcases inT2_cases_of_center_bot hT hcen with ⟨p', f', hp', hf', ⟨hodd, -⟩, hmodel⟩ | he
  · have hp'2 : p' ≠ 2 := by
      rintro rfl
      have : Even (2 ^ f') := Nat.even_pow.2 ⟨even_two, by omega⟩
      exact (Nat.not_even_iff_odd.2 hodd) this
    exact l3_ne_L2 ht hp hp2 hq h hp' hp'2 hmodel
  · obtain ⟨e⟩ := he
    have h2 := Nat.card_congr e.toEquiv
    have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [h7] at h2
    omega

theorem l3_not_inC2
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) [Finite X]
    (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hP : Gen4Comp X) (h : LieModel X t 3 p f) : ¬ InC2 X := by
  intro hC
  have hmod : LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f := by
    rcases ht with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  have hcen : center X = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hC.1 hmod
  obtain ⟨h1, -, -⟩ := l3_card_bounds ht hp hp2 hq h
  have hc1 : Nat.card (center X) = 1 := by rw [hcen, Subgroup.card_bot]
  rcases c2Shape_of_inC2 hG hF hC hP with ⟨-, hshape⟩ | h2m | h2s
  · rcases hshape with ⟨p', f', hp', hp'2, -, hmodel⟩ | hL28 | hL33 | hU33 | hSz8 | hM11
    · exact l3_ne_L2 ht hp hp2 hq h hp' hp'2 hmodel
    · have hc := card_of_lieModel_PSL (n := 2) (by norm_num) hL28
      have : Nat.card X = 504 := by rw [hc]; decide
      omega
    · have hc := card_of_lieModel_PSL (n := 3) (by norm_num) hL33
      have : Nat.card X = 5616 := by rw [hc]; decide
      omega
    · have hc := card_of_lieModel_PSU (n := 3) (by norm_num) (by norm_num) hU33
      have : Nat.card X = 6048 := by rw [hc]; decide
      omega
    · have hc := card_of_lieModel_twistedB2 hSz8
      have : Nat.card X = 29120 := by rw [hc]; decide
      omega
    · have hc := card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hM11
      omega
  · have := h2m.2.1
    omega
  · have := h2s.2.1
    omega

theorem l3_not_inC2_not_inT2
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) [Finite X]
    (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hP : Gen4Comp X) (h : LieModel X t 3 p f) : ¬ InC2 X ∧ ¬ InT2 X :=
  ⟨l3_not_inC2 hG hF ht hp hp2 hq hP h, l3_not_inT2 ht hp hp2 hq h⟩

end Groups

end CFSG.GH74.Generic.S3
