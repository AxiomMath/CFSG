module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PSp

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG P211

theorem v2_odd' {x : ℕ} (hx : ¬ 2 ∣ x) : padicValNat 2 x = 0 :=
  padicValNat.eq_zero_of_not_dvd hx

theorem v2_cube_sub {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (q ^ 3 - 1) = padicValNat 2 (q - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ q)]
    ring
  obtain ⟨k, rfl⟩ := hq
  rw [h1, padicValNat.mul (by omega) (by positivity), v2_odd' (x := (2 * k + 1) ^ 2 + _ + 1)
    (by rw [Nat.dvd_iff_mod_eq_zero]; ring_nf; omega), add_zero]

theorem v2_cube_add {q : ℕ} (hq : Odd q) :
    padicValNat 2 (q ^ 3 + 1) = padicValNat 2 (q + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    have : q ≤ q ^ 2 := by nlinarith
    zify [this]
    ring
  obtain ⟨k, rfl⟩ := hq
  have hk : (2 * k + 1) ≤ (2 * k + 1) ^ 2 := by nlinarith
  rw [h1, padicValNat.mul (by omega) (by omega), v2_odd' (x := (2 * k + 1) ^ 2 - _ + 1), add_zero]
  intro h
  obtain ⟨c, hc⟩ := h
  have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
  omega

theorem v2_fifth_sub {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (q ^ 5 - 1) = padicValNat 2 (q - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : q ^ 5 - 1 = (q - 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) := by
    have : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ q)]
    ring
  obtain ⟨k, rfl⟩ := hq
  rw [h1, padicValNat.mul (by omega) (by positivity), v2_odd'
    (x := (2 * k + 1) ^ 4 + (2 * k + 1) ^ 3 + (2 * k + 1) ^ 2 + (2 * k + 1) + 1)
    (by rw [Nat.dvd_iff_mod_eq_zero]; ring_nf; omega), add_zero]

theorem v2_fifth_add {q : ℕ} (hq : Odd q) :
    padicValNat 2 (q ^ 5 + 1) = padicValNat 2 (q + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 5 + 1 = ((2 * k + 1) + 1) *
      (16 * k ^ 4 + 24 * k ^ 3 + 16 * k ^ 2 + 4 * k + 1) := by ring
  rw [h1, padicValNat.mul (by omega) (by positivity),
    v2_odd' (x := 16 * k ^ 4 + 24 * k ^ 3 + 16 * k ^ 2 + 4 * k + 1) (by omega), add_zero]

theorem v2_sq_sub {q : ℕ} (hq3 : 3 ≤ q) :
    padicValNat 2 (q ^ 2 - 1) = padicValNat 2 (q - 1) + padicValNat 2 (q + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this, (by omega : 1 ≤ q)]
    ring
  rw [h1, padicValNat.mul (by omega) (by omega)]

theorem v2_sub_of_mod_four {q : ℕ} (hq : q % 4 = 3) : padicValNat 2 (q - 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ : ∃ k, q - 1 = 2 * (2 * k + 1) := ⟨q / 4, by omega⟩
  rw [hk, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    v2_odd' (by omega)]

theorem v2_add_of_mod_four {q : ℕ} (hq : q % 4 = 1) : padicValNat 2 (q + 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ : ∃ k, q + 1 = 2 * (2 * k + 1) := ⟨q / 4, by omega⟩
  rw [hk, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    v2_odd' (by omega)]

theorem ordA_mul_gcd {n q : ℕ} (hn : 1 ≤ n) (hq1 : 1 ≤ q) :
    Open.ordA n q * Nat.gcd (n + 1) (q - 1) =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) := by
  rw [Open.ordA]
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left ?_ _))
  have h2 : q - 1 ∣ q ^ 2 - 1 := ⟨q + 1, by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this, hq1]
    ring⟩
  exact h2.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))

theorem v2_ordA_eq {n q : ℕ} (hn : 1 ≤ n) (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (Open.ordA n q) + padicValNat 2 (Nat.gcd (n + 1) (q - 1)) =
      padicValNat 2 (∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprod : ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => by
      have : 1 < q ^ i := Nat.one_lt_pow (by have := (Finset.mem_Icc.mp hi).1; omega) (by omega)
      omega
  have hg : Nat.gcd (n + 1) (q - 1) ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have h1 := congrArg (padicValNat 2) (ordA_mul_gcd (q := q) hn (by omega))
  have hA : Open.ordA n q ≠ 0 := by
    intro h0
    have := ordA_mul_gcd (q := q) hn (by omega)
    rw [h0, zero_mul] at this
    exact Nat.mul_ne_zero (by positivity) hprod this.symm
  have hq0 : padicValNat 2 (q ^ (n * (n + 1) / 2)) = 0 := by
    rw [padicValNat.pow, v2_odd hq, mul_zero]
  rw [padicValNat.mul hA hg, padicValNat.mul (by positivity) hprod, hq0, zero_add] at h1
  exact h1

theorem pow_sub_one_ne_zero {q i : ℕ} (hq : 2 ≤ q) (hi : i ≠ 0) : q ^ i - 1 ≠ 0 := by
  have := Nat.one_lt_pow hi (by omega : 1 < q)
  omega

theorem v2_gcd_odd {k x : ℕ} (hk : ¬ 2 ∣ k) : padicValNat 2 (Nat.gcd k x) = 0 :=
  v2_odd' fun h => hk (h.trans (Nat.gcd_dvd_left k x))

theorem v2_ordA_one {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (Open.ordA 1 q) + 1 = padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := v2_ordA_eq (n := 1) le_rfl hq hq3
  have hg : Nat.gcd (1 + 1) (q - 1) = 2 := by
    obtain ⟨k, rfl⟩ := hq
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_mul_right_right k 2
  rw [hg, padicValNat.self (by norm_num), show Finset.Icc 2 (1 + 1) = {2} from rfl,
    Finset.prod_singleton] at h
  exact h

theorem v2_ordA_two {q : ℕ} (hq4 : q % 4 = 3) :
    padicValNat 2 (Open.ordA 2 q) = padicValNat 2 (q ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Odd q := ⟨q / 2, by omega⟩
  have hq3 : 3 ≤ q := by omega
  have h := v2_ordA_eq (n := 2) (by norm_num) hq hq3
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h3 : q ^ 3 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  rw [v2_gcd_odd (by norm_num), show Finset.Icc 2 (2 + 1) = {2, 3} from rfl,
    Finset.prod_pair (by norm_num), padicValNat.mul h2 h3, v2_cube_sub hq hq3,
    v2_sub_of_mod_four hq4] at h
  omega

theorem v2_ordA_three {q : ℕ} (hq4 : q % 4 = 3) :
    padicValNat 2 (Open.ordA 3 q) = 2 * padicValNat 2 (q ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Odd q := ⟨q / 2, by omega⟩
  have hq3 : 3 ≤ q := by omega
  have h := v2_ordA_eq (n := 3) (by norm_num) hq hq3
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h3 : q ^ 3 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have hg : Nat.gcd (3 + 1) (q - 1) = 2 := by
    rw [Nat.gcd_rec, show (q - 1) % (3 + 1) = 2 by omega]
    rfl
  rw [hg, padicValNat.self (by norm_num), show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl,
    Finset.prod_insert (by decide), Finset.prod_pair (by norm_num), padicValNat.mul h2
    (Nat.mul_ne_zero h3 h4), padicValNat.mul h3 h4, v2_cube_sub hq hq3, v2_four hq hq3,
    v2_sub_of_mod_four hq4] at h
  omega

theorem v2_ordA_four {q : ℕ} (hq4 : q % 4 = 3) :
    padicValNat 2 (Open.ordA 4 q) = 2 * padicValNat 2 (q ^ 2 - 1) + 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Odd q := ⟨q / 2, by omega⟩
  have hq3 : 3 ≤ q := by omega
  have h := v2_ordA_eq (n := 4) (by norm_num) hq hq3
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h3 : q ^ 3 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h5 : q ^ 5 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  rw [v2_gcd_odd (by norm_num), show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} from rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair
    (by norm_num), padicValNat.mul h2 (Nat.mul_ne_zero h3 (Nat.mul_ne_zero h4 h5)),
    padicValNat.mul h3 (Nat.mul_ne_zero h4 h5), padicValNat.mul h4 h5, v2_cube_sub hq hq3,
    v2_four hq hq3, v2_fifth_sub hq hq3, v2_sub_of_mod_four hq4] at h
  omega

theorem toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have h : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [this]; ring
  rw [h, Int.toNat_natCast]

theorem toNat_odd {q i : ℕ} (hi : Odd i) : ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  have h : ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

theorem add_dvd_cube_add (q : ℕ) : q + 1 ∣ q ^ 3 + 1 :=
  ⟨q ^ 2 - q + 1, by
    have : q ≤ q ^ 2 := by nlinarith
    zify [this]
    ring⟩

theorem ordTwistedA_two_mul {q : ℕ} (hq1 : 1 ≤ q) :
    Open.ordTwistedA 2 q * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  rw [Open.ordTwistedA, show Finset.Icc 2 (2 + 1) = {2, 3} from rfl, Finset.prod_pair
    (by norm_num), toNat_even hq1 (by decide), toNat_odd (by decide),
    show 2 * (2 + 1) / 2 = 3 from rfl, show (2 : ℕ) + 1 = 3 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (add_dvd_cube_add q) _) _))

theorem ordTwistedA_three_mul {q : ℕ} (hq1 : 1 ≤ q) :
    Open.ordTwistedA 3 q * Nat.gcd 4 (q + 1) =
      q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) := by
  rw [Open.ordTwistedA, show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl, Finset.prod_insert
    (by decide), Finset.prod_pair (by norm_num), toNat_even hq1 (by decide),
    toNat_odd (by decide), toNat_even hq1 (by decide), show 3 * (3 + 1) / 2 = 6 from rfl,
    show (3 : ℕ) + 1 = 4 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right (add_dvd_cube_add q) _) _) _))

theorem ordTwistedA_four_mul {q : ℕ} (hq1 : 1 ≤ q) :
    Open.ordTwistedA 4 q * Nat.gcd 5 (q + 1) =
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) := by
  rw [Open.ordTwistedA, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} from rfl, Finset.prod_insert
    (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
    toNat_even hq1 (by decide), toNat_odd (by decide), toNat_even hq1 (by decide),
    toNat_odd (by decide), show 4 * (4 + 1) / 2 = 10 from rfl, show (4 : ℕ) + 1 = 5 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right (add_dvd_cube_add q) _) _) _))

theorem v2_ordTwistedA_two {q : ℕ} (hq4 : q % 4 = 1) (hq5 : 5 ≤ q) :
    padicValNat 2 (Open.ordTwistedA 2 q) = padicValNat 2 (q ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Odd q := ⟨q / 2, by omega⟩
  have h := congrArg (padicValNat 2) (ordTwistedA_two_mul (q := q) (by omega))
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have hA : Open.ordTwistedA 2 q ≠ 0 := by
    intro h0
    have := ordTwistedA_two_mul (q := q) (by omega)
    rw [h0, zero_mul] at this
    exact Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero h2 (by positivity)) this.symm
  rw [padicValNat.mul hA (Nat.gcd_ne_zero_right (by omega)), v2_gcd_odd (by norm_num),
    padicValNat.mul (by positivity) (Nat.mul_ne_zero h2 (by positivity)), padicValNat.pow,
    v2_odd hq, padicValNat.mul h2 (by positivity), v2_cube_add hq,
    v2_add_of_mod_four hq4] at h
  omega

theorem v2_ordTwistedA_three {q : ℕ} (hq4 : q % 4 = 1) (hq5 : 5 ≤ q) :
    padicValNat 2 (Open.ordTwistedA 3 q) = 2 * padicValNat 2 (q ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Odd q := ⟨q / 2, by omega⟩
  have h := congrArg (padicValNat 2) (ordTwistedA_three_mul (q := q) (by omega))
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have hP : (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) ≠ 0 :=
    Nat.mul_ne_zero h2 (Nat.mul_ne_zero (by positivity) h4)
  have hA : Open.ordTwistedA 3 q ≠ 0 := by
    intro h0
    have := ordTwistedA_three_mul (q := q) (by omega)
    rw [h0, zero_mul] at this
    exact Nat.mul_ne_zero (by positivity) hP this.symm
  have hg : Nat.gcd 4 (q + 1) = 2 := by
    rw [Nat.gcd_rec, show (q + 1) % 4 = 2 by omega]
    rfl
  rw [padicValNat.mul hA (Nat.gcd_ne_zero_right (by omega)), hg, padicValNat.self (by norm_num),
    padicValNat.mul (by positivity) hP, padicValNat.pow, v2_odd hq,
    padicValNat.mul h2 (Nat.mul_ne_zero (by positivity) h4), padicValNat.mul (by positivity) h4,
    v2_cube_add hq, v2_four hq (by omega), v2_add_of_mod_four hq4] at h
  omega

theorem v2_ordTwistedA_four {q : ℕ} (hq4 : q % 4 = 1) (hq5 : 5 ≤ q) :
    padicValNat 2 (Open.ordTwistedA 4 q) = 2 * padicValNat 2 (q ^ 2 - 1) + 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Odd q := ⟨q / 2, by omega⟩
  have h := congrArg (padicValNat 2) (ordTwistedA_four_mul (q := q) (by omega))
  have h2 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h4 : q ^ 4 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h45 : (q ^ 4 - 1) * (q ^ 5 + 1) ≠ 0 := Nat.mul_ne_zero h4 (by positivity)
  have h345 : (q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)) ≠ 0 :=
    Nat.mul_ne_zero (by positivity) h45
  have hP : (q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1))) ≠ 0 :=
    Nat.mul_ne_zero h2 h345
  have hA : Open.ordTwistedA 4 q ≠ 0 := by
    intro h0
    have := ordTwistedA_four_mul (q := q) (by omega)
    rw [h0, zero_mul] at this
    exact Nat.mul_ne_zero (by positivity) hP this.symm
  rw [padicValNat.mul hA (Nat.gcd_ne_zero_right (by omega)), v2_gcd_odd (by norm_num),
    padicValNat.mul (by positivity) hP, padicValNat.pow, v2_odd hq, padicValNat.mul h2 h345,
    padicValNat.mul (by positivity) h45, padicValNat.mul h4 (by positivity), v2_cube_add hq,
    v2_four hq (by omega), v2_fifth_add hq, v2_add_of_mod_four hq4] at h
  omega

end P211X

end CFSG.ComponentClassification.GSThmB
