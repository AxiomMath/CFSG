module

public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts
public import CFSG.Open.Defs

public section

namespace CFSG.OddStandard.ThmC.Sylow

open CFSG.Open CFSG.OddStandard.ThmC.T

theorem two_pow_six_dvd_of_isT {K : Type*} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) : 2 ^ 6 ∣ Nat.card K := by
  have h := (T : Subgroup K).card_mul_index
  rw [hT.card_eq] at h
  exact ⟨(T : Subgroup K).index, by rw [← h]; norm_num⟩

theorem not_two_pow_seven_dvd_of_isT {K : Type*} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) : ¬ 2 ^ 7 ∣ Nat.card K := by
  have h := (T : Subgroup K).card_mul_index
  rw [hT.card_eq] at h
  intro hdvd
  rw [← h, show (2 : ℕ) ^ 7 = 64 * 2 by norm_num] at hdvd
  exact T.not_dvd_index (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)

theorem false_of_two_pow_seven_dvd {K : Type*} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) (h : 2 ^ 7 ∣ Nat.card K) : False :=
  not_two_pow_seven_dvd_of_isT T hT h

theorem false_of_not_two_pow_six_dvd {K : Type*} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) (h : ¬ 2 ^ 6 ∣ Nat.card K) : False :=
  h (two_pow_six_dvd_of_isT T hT)

theorem dvd_of_cast_eq_zero {n a : ℕ} (h : (a : ZMod n) = 0) : n ∣ a :=
  (ZMod.natCast_eq_zero_iff a n).1 h

theorem cast_pow_sub_one {n q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    ((q ^ i - 1 : ℕ) : ZMod n) = (q : ZMod n) ^ i - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  simp

theorem toNat_pow_sub_neg_one_even {q i : ℕ} (hi : Even i) :
    (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have h : ((q : ℤ) ^ i) = ((q ^ i : ℕ) : ℤ) := by push_cast; rfl
  rw [h]
  omega

theorem toNat_pow_sub_neg_one_odd {q i : ℕ} (hi : Odd i) :
    (((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) = q ^ i + 1 := by
  rw [hi.neg_one_pow]
  have h : ((q : ℤ) ^ i) = ((q ^ i : ℕ) : ℤ) := by push_cast; rfl
  rw [h]
  omega

theorem gcd_four_sub_one_of_mod_one {q : ℕ} (h : q % 4 = 1) : Nat.gcd 4 (q - 1) = 4 :=
  Nat.gcd_eq_left (by omega)

theorem gcd_four_sub_one_of_mod_three {q : ℕ} (h : q % 4 = 3) : Nat.gcd 4 (q - 1) = 2 := by
  have h2 : (q - 1) % 4 = 2 := by omega
  rw [Nat.gcd_rec, h2]
  rfl

theorem gcd_four_add_one_of_mod_three {q : ℕ} (h : q % 4 = 3) : Nat.gcd 4 (q + 1) = 4 :=
  Nat.gcd_eq_left (by omega)

theorem gcd_four_add_one_of_mod_one {q : ℕ} (h : q % 4 = 1) : Nat.gcd 4 (q + 1) = 2 := by
  have h2 : (q + 1) % 4 = 2 := by omega
  rw [Nat.gcd_rec, h2]
  rfl

theorem ordA_three_eq (q : ℕ) :
    ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q - 1) := by
  simp [ordA, Finset.prod_Icc_succ_top, Nat.mul_assoc]

theorem zmod512_psl4 : ∀ x : ZMod 512, x.val % 4 = 1 →
    x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 - 1) * (x ^ 4 - 1)) = 0 := by decide +kernel

theorem zmod256_psl4 : ∀ x : ZMod 256, x.val % 4 = 3 →
    x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 - 1) * (x ^ 4 - 1)) = 0 := by decide +kernel

theorem dvd_psl4_numerator {n q : ℕ} (hq : 1 ≤ q)
    (h : (q : ZMod n) ^ 6 * (((q : ZMod n) ^ 2 - 1) * ((q : ZMod n) ^ 3 - 1) *
      ((q : ZMod n) ^ 4 - 1)) = 0) : n ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
  apply dvd_of_cast_eq_zero
  push_cast [cast_pow_sub_one hq]
  exact h

theorem two_pow_seven_dvd_ordA_three {q : ℕ} (hq : Odd q) : 2 ^ 7 ∣ ordA 3 q := by
  have hq1 : 1 ≤ q := hq.pos
  rw [ordA_three_eq]
  apply Nat.dvd_div_of_mul_dvd
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨m, rfl⟩ := hq
    omega
  rcases hmod with h | h
  · rw [gcd_four_sub_one_of_mod_one h, show 4 * (2 : ℕ) ^ 7 = 512 by norm_num]
    exact dvd_psl4_numerator hq1 (zmod512_psl4 _ (by rw [ZMod.val_natCast]; omega))
  · rw [gcd_four_sub_one_of_mod_three h, show 2 * (2 : ℕ) ^ 7 = 256 by norm_num]
    exact dvd_psl4_numerator hq1 (zmod256_psl4 _ (by rw [ZMod.val_natCast]; omega))

theorem ordTwistedA_three_eq (q : ℕ) :
    ordTwistedA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q + 1) := by
  have h2 := toNat_pow_sub_neg_one_even (q := q) (i := 2) (by decide)
  have h3 := toNat_pow_sub_neg_one_odd (q := q) (i := 3) (by decide)
  have h4 := toNat_pow_sub_neg_one_even (q := q) (i := 4) (by decide)
  have hI : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
  unfold ordTwistedA
  rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton, h2, h3, h4]
  simp [Nat.mul_assoc]

theorem zmod512_psu4 : ∀ x : ZMod 512, x.val % 4 = 3 →
    x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) = 0 := by decide +kernel

theorem zmod256_psu4 : ∀ x : ZMod 256, x.val % 4 = 1 →
    x ^ 6 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1)) = 0 := by decide +kernel

theorem dvd_psu4_numerator {n q : ℕ} (hq : 1 ≤ q)
    (h : (q : ZMod n) ^ 6 * (((q : ZMod n) ^ 2 - 1) * ((q : ZMod n) ^ 3 + 1) *
      ((q : ZMod n) ^ 4 - 1)) = 0) : n ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
  apply dvd_of_cast_eq_zero
  push_cast [cast_pow_sub_one hq]
  exact h

theorem two_pow_seven_dvd_ordTwistedA_three {q : ℕ} (hq : Odd q) : 2 ^ 7 ∣ ordTwistedA 3 q := by
  have hq1 : 1 ≤ q := hq.pos
  rw [ordTwistedA_three_eq q]
  apply Nat.dvd_div_of_mul_dvd
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨m, rfl⟩ := hq
    omega
  rcases hmod with h | h
  · rw [gcd_four_add_one_of_mod_one h, show 2 * (2 : ℕ) ^ 7 = 256 by norm_num]
    exact dvd_psu4_numerator hq1 (zmod256_psu4 _ (by rw [ZMod.val_natCast]; omega))
  · rw [gcd_four_add_one_of_mod_three h, show 4 * (2 : ℕ) ^ 7 = 512 by norm_num]
    exact dvd_psu4_numerator hq1 (zmod512_psu4 _ (by rw [ZMod.val_natCast]; omega))

theorem ordA_four_eq (q : ℕ) :
    ordA 4 q = q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)) /
      Nat.gcd 5 (q - 1) := by
  simp [ordA, Finset.prod_Icc_succ_top, Nat.mul_assoc]

theorem zmod128_psl5 : ∀ x : ZMod 128, x.val % 2 = 1 →
    x ^ 10 * ((x ^ 2 - 1) * (x ^ 3 - 1) * (x ^ 4 - 1) * (x ^ 5 - 1)) = 0 := by decide +kernel

theorem coprime_two_pow_of_dvd_five {g : ℕ} (hg : g ∣ 5) (k : ℕ) : Nat.Coprime (2 ^ k) g :=
  Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right hg (by norm_num))

theorem two_pow_seven_dvd_ordA_four {q : ℕ} (hq : Odd q) : 2 ^ 7 ∣ ordA 4 q := by
  have hq1 : 1 ≤ q := hq.pos
  rw [ordA_four_eq]
  set N := q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) * (q ^ 5 - 1)) with hN
  have h128 : 2 ^ 7 ∣ N := by
    refine dvd_of_cast_eq_zero (n := 2 ^ 7) ?_
    rw [hN]
    push_cast [cast_pow_sub_one hq1]
    exact zmod128_psl5 _ (by rw [ZMod.val_natCast]; obtain ⟨m, rfl⟩ := hq; omega)
  have hsub : (q - 1) ∣ q ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow q 1 2
    simpa using this
  have hgN : Nat.gcd 5 (q - 1) ∣ N := by
    refine Dvd.dvd.mul_left ?_ _
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      ((Nat.gcd_dvd_right 5 (q - 1)).trans hsub) _) _) _
  have hcop := coprime_two_pow_of_dvd_five (Nat.gcd_dvd_left 5 (q - 1)) 7
  rw [← Nat.mul_div_cancel' hgN] at h128
  exact hcop.dvd_of_dvd_mul_left h128

theorem ordTwistedA_four_eq (q : ℕ) :
    ordTwistedA 4 q = q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) /
      Nat.gcd 5 (q + 1) := by
  have h2 := toNat_pow_sub_neg_one_even (q := q) (i := 2) (by decide)
  have h3 := toNat_pow_sub_neg_one_odd (q := q) (i := 3) (by decide)
  have h4 := toNat_pow_sub_neg_one_even (q := q) (i := 4) (by decide)
  have h5 := toNat_pow_sub_neg_one_odd (q := q) (i := 5) (by decide)
  have hI : Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} := by decide
  unfold ordTwistedA
  rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, h2, h3, h4, h5]
  simp [Nat.mul_assoc]

theorem zmod128_psu5 : ∀ x : ZMod 128, x.val % 2 = 1 →
    x ^ 10 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1)) = 0 := by decide +kernel

theorem two_pow_seven_dvd_ordTwistedA_four {q : ℕ} (hq : Odd q) : 2 ^ 7 ∣ ordTwistedA 4 q := by
  have hq1 : 1 ≤ q := hq.pos
  rw [ordTwistedA_four_eq]
  set N := q ^ 10 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) * (q ^ 5 + 1)) with hN
  have h128 : 2 ^ 7 ∣ N := by
    refine dvd_of_cast_eq_zero (n := 2 ^ 7) ?_
    rw [hN]
    push_cast [cast_pow_sub_one hq1]
    exact zmod128_psu5 _ (by rw [ZMod.val_natCast]; obtain ⟨m, rfl⟩ := hq; omega)
  have hadd : (q + 1) ∣ q ^ 3 + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    simpa using this
  have hgN : Nat.gcd 5 (q + 1) ∣ N := by
    refine Dvd.dvd.mul_left ?_ _
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left
      ((Nat.gcd_dvd_right 5 (q + 1)).trans hadd) _) _) _
  have hcop := coprime_two_pow_of_dvd_five (Nat.gcd_dvd_left 5 (q + 1)) 7
  rw [← Nat.mul_div_cancel' hgN] at h128
  exact hcop.dvd_of_dvd_mul_left h128

theorem three_pow_odd_mod_eight (k : ℕ) : 3 ^ (2 * k + 1) % 8 = 3 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem zmod16_ree : ∀ x : ZMod 16, x.val % 8 = 3 → x ^ 3 * (x ^ 3 + 1) * (x - 1) = 8 := by
  decide +kernel

theorem not_two_pow_six_dvd_ordRee (k : ℕ) : ¬ 2 ^ 6 ∣ ordRee (3 ^ (2 * k + 1)) := by
  intro h
  have hq1 : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h16 : 16 ∣ ordRee (3 ^ (2 * k + 1)) := (by norm_num : 16 ∣ 2 ^ 6).trans h
  have hz := (ZMod.natCast_eq_zero_iff _ 16).2 h16
  unfold ordRee at hz
  push_cast [Nat.cast_sub hq1] at hz
  have hv : ((3 : ZMod 16) ^ (2 * k + 1)).val % 8 = 3 := by
    have := ZMod.val_natCast (n := 16) (3 ^ (2 * k + 1))
    push_cast at this
    rw [this]
    have h8 := three_pow_odd_mod_eight k
    omega
  rw [zmod16_ree _ hv] at hz
  revert hz
  decide +kernel

theorem ordA_one_eight : ordA 1 8 = 504 := by decide +kernel

theorem ordA_one_sixteen : ordA 1 16 = 4080 := by decide +kernel

end CFSG.OddStandard.ThmC.Sylow
