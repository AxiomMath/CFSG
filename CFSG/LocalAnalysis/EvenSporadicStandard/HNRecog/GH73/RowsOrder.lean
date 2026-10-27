module

public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.Blueprint CFSG.GH74
open CFSG.Open (ordA ordTwistedA ordBC ordRee)

variable {X : Type} [Group X]

private theorem gh73x_eight_dvd_sq {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring_nf; omega
  rw [h]
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  rw [hj]
  exact ⟨j, by ring⟩

private theorem gh73x_sixteen_dvd_fourth {q : ℕ} (hq : Odd q) : 16 ∣ q ^ 4 - 1 := by
  have hq1 : 1 ≤ q := hq.pos
  have h1 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 4 q hq1, Nat.one_le_pow 2 q hq1]
    ring
  have h2 : 2 ∣ q ^ 2 + 1 := by
    obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
    omega
  rw [h1]
  exact Dvd.dvd.trans (by norm_num : 16 ∣ 8 * 2) (Nat.mul_dvd_mul (gh73x_eight_dvd_sq hq) h2)

private theorem gh73x_two_dvd_cube_sub {q : ℕ} (hq : Odd q) : 2 ∣ q ^ 3 - 1 := by
  obtain ⟨k, hk⟩ : Odd (q ^ 3) := hq.pow
  omega

private theorem gh73x_two_dvd_cube_add {q : ℕ} (hq : Odd q) : 2 ∣ q ^ 3 + 1 := by
  obtain ⟨k, hk⟩ : Odd (q ^ 3) := hq.pow
  omega

private theorem gh73x_add_dvd_cube (q : ℕ) : q + 1 ∣ q ^ 3 + 1 :=
  ⟨q ^ 2 - q + 1, by
    have : q ≤ q ^ 2 := by nlinarith
    zify [this]
    ring⟩

private theorem gh73x_P_dvd {q : ℕ} (hq : Odd q) :
    256 ∣ (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) :=
  Dvd.dvd.trans (by norm_num : 256 ∣ 8 * (2 * 16))
    (Nat.mul_dvd_mul (gh73x_eight_dvd_sq hq) (Nat.mul_dvd_mul (gh73x_two_dvd_cube_sub hq)
      (gh73x_sixteen_dvd_fourth hq)))

private theorem gh73x_P_dvd' {q : ℕ} (hq : Odd q) (h4 : 4 ∣ q - 1) :
    512 ∣ (q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)) :=
  Dvd.dvd.trans (by norm_num : 512 ∣ 8 * (4 * 16))
    (Nat.mul_dvd_mul (gh73x_eight_dvd_sq hq) (Nat.mul_dvd_mul
      (h4.trans (Nat.sub_one_dvd_pow_sub_one q 3)) (gh73x_sixteen_dvd_fourth hq)))

private theorem gh73x_U_dvd {q : ℕ} (hq : Odd q) :
    256 ∣ (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) :=
  Dvd.dvd.trans (by norm_num : 256 ∣ 8 * (2 * 16))
    (Nat.mul_dvd_mul (gh73x_eight_dvd_sq hq) (Nat.mul_dvd_mul (gh73x_two_dvd_cube_add hq)
      (gh73x_sixteen_dvd_fourth hq)))

private theorem gh73x_U_dvd' {q : ℕ} (hq : Odd q) (h4 : 4 ∣ q + 1) :
    512 ∣ (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) :=
  Dvd.dvd.trans (by norm_num : 512 ∣ 8 * (4 * 16))
    (Nat.mul_dvd_mul (gh73x_eight_dvd_sq hq) (Nat.mul_dvd_mul (h4.trans (gh73x_add_dvd_cube q))
      (gh73x_sixteen_dvd_fourth hq)))

private theorem gh73x_toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have h : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [this]; ring
  rw [h, Int.toNat_natCast]

private theorem gh73x_toNat_odd {q i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  have h : ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

private theorem gh73x_ordA_three_mul (q : ℕ) :
    ordA 3 q * Nat.gcd 4 (q - 1) = q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := by
  have hdvd : Nat.gcd 4 (q - 1) ∣ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) :=
    (Nat.gcd_dvd_right 4 (q - 1)).trans
      (((Nat.sub_one_dvd_pow_sub_one q 2).mul_right _).mul_left _)
  rw [ordA, show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num), show 3 * (3 + 1) / 2 = 6 from rfl,
    show (3 : ℕ) + 1 = 4 from rfl]
  exact Nat.div_mul_cancel hdvd

private theorem gh73x_ordA_four_mul (q : ℕ) :
    ordA 4 q * Nat.gcd 5 (q - 1) =
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) := by
  have hdvd : Nat.gcd 5 (q - 1) ∣
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1)))) :=
    (Nat.gcd_dvd_right 5 (q - 1)).trans
      (((Nat.sub_one_dvd_pow_sub_one q 2).mul_right _).mul_left _)
  rw [ordA, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} from rfl, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
    show 4 * (4 + 1) / 2 = 10 from rfl, show (4 : ℕ) + 1 = 5 from rfl]
  exact Nat.div_mul_cancel hdvd

private theorem gh73x_ordTwistedA_three_mul {q : ℕ} (hq1 : 1 ≤ q) :
    ordTwistedA 3 q * Nat.gcd 4 (q + 1) =
      q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) := by
  rw [ordTwistedA, show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl, Finset.prod_insert
    (by decide), Finset.prod_pair (by norm_num), gh73x_toNat_even hq1 (by decide),
    gh73x_toNat_odd (by decide), gh73x_toNat_even hq1 (by decide),
    show 3 * (3 + 1) / 2 = 6 from rfl, show (3 : ℕ) + 1 = 4 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right (gh73x_add_dvd_cube q) _) _) _))

private theorem gh73x_ordTwistedA_four_mul {q : ℕ} (hq1 : 1 ≤ q) :
    ordTwistedA 4 q * Nat.gcd 5 (q + 1) =
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) := by
  rw [ordTwistedA, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} from rfl, Finset.prod_insert
    (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
    gh73x_toNat_even hq1 (by decide), gh73x_toNat_odd (by decide), gh73x_toNat_even hq1 (by decide),
    gh73x_toNat_odd (by decide), show 4 * (4 + 1) / 2 = 10 from rfl, show (4 : ℕ) + 1 = 5 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right (gh73x_add_dvd_cube q) _) _) _))

private theorem gh73x_dvd_ordA_three {q : ℕ} (hq : Odd q) : 128 ∣ ordA 3 q := by
  have hq1 : 1 ≤ q := hq.pos
  have hm := gh73x_ordA_three_mul q
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    have := Nat.odd_iff.mp hq
    omega
  rcases hmod with h | h
  · have h4 : 4 ∣ q - 1 := by omega
    have hg : Nat.gcd 4 (q - 1) = 4 := Nat.gcd_eq_left h4
    have hd : 512 ∣ ordA 3 q * Nat.gcd 4 (q - 1) := by
      rw [hm]
      exact Dvd.dvd.mul_left (gh73x_P_dvd' hq h4) _
    rw [hg] at hd
    omega
  · have hg : Nat.gcd 4 (q - 1) = 2 := by
      have h2 : (q - 1) % 4 = 2 := by omega
      rw [Nat.gcd_rec, h2]
      rfl
    have hd : 256 ∣ ordA 3 q * Nat.gcd 4 (q - 1) := by
      rw [hm]
      exact Dvd.dvd.mul_left (gh73x_P_dvd hq) _
    rw [hg] at hd
    omega

private theorem gh73x_dvd_ordTwistedA_three {q : ℕ} (hq : Odd q) : 128 ∣ ordTwistedA 3 q := by
  have hq1 : 1 ≤ q := hq.pos
  have hm := gh73x_ordTwistedA_three_mul hq1
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    have := Nat.odd_iff.mp hq
    omega
  rcases hmod with h | h
  · have hg : Nat.gcd 4 (q + 1) = 2 := by
      have h2 : (q + 1) % 4 = 2 := by omega
      rw [Nat.gcd_rec, h2]
      rfl
    have hd : 256 ∣ ordTwistedA 3 q * Nat.gcd 4 (q + 1) := by
      rw [hm]
      exact Dvd.dvd.mul_left (gh73x_U_dvd hq) _
    rw [hg] at hd
    omega
  · have h4 : 4 ∣ q + 1 := by omega
    have hg : Nat.gcd 4 (q + 1) = 4 := Nat.gcd_eq_left h4
    have hd : 512 ∣ ordTwistedA 3 q * Nat.gcd 4 (q + 1) := by
      rw [hm]
      exact Dvd.dvd.mul_left (gh73x_U_dvd' hq h4) _
    rw [hg] at hd
    omega

private theorem gh73x_dvd_ordA_four {q : ℕ} (hq : Odd q) : 128 ∣ ordA 4 q := by
  have hm := gh73x_ordA_four_mul q
  have hP : 256 ∣ (q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1))) :=
    Dvd.dvd.trans (by norm_num : 256 ∣ 8 * (2 * 16)) (Nat.mul_dvd_mul (gh73x_eight_dvd_sq hq)
      (Nat.mul_dvd_mul (gh73x_two_dvd_cube_sub hq) ((gh73x_sixteen_dvd_fourth hq).mul_right _)))
  have hg : Nat.gcd 5 (q - 1) = 1 ∨ Nat.gcd 5 (q - 1) = 5 :=
    (Nat.dvd_prime Nat.prime_five).mp (Nat.gcd_dvd_left 5 (q - 1))
  have hd : 256 ∣ ordA 4 q * Nat.gcd 5 (q - 1) := by
    rw [hm]
    exact Dvd.dvd.mul_left hP _
  rcases hg with hg | hg <;> rw [hg] at hd <;> omega

private theorem gh73x_dvd_ordTwistedA_four {q : ℕ} (hq : Odd q) : 128 ∣ ordTwistedA 4 q := by
  have hq1 : 1 ≤ q := hq.pos
  have hm := gh73x_ordTwistedA_four_mul hq1
  have hP : 256 ∣ (q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1))) :=
    Dvd.dvd.trans (by norm_num : 256 ∣ 8 * (2 * 16)) (Nat.mul_dvd_mul (gh73x_eight_dvd_sq hq)
      (Nat.mul_dvd_mul (gh73x_two_dvd_cube_add hq) ((gh73x_sixteen_dvd_fourth hq).mul_right _)))
  have hg : Nat.gcd 5 (q + 1) = 1 ∨ Nat.gcd 5 (q + 1) = 5 :=
    (Nat.dvd_prime Nat.prime_five).mp (Nat.gcd_dvd_left 5 (q + 1))
  have hd : 256 ∣ ordTwistedA 4 q * Nat.gcd 5 (q + 1) := by
    rw [hm]
    exact Dvd.dvd.mul_left hP _
  rcases hg with hg | hg <;> rw [hg] at hd <;> omega

private theorem gh73x_pow_three_mod (k : ℕ) :
    3 ^ (2 * k + 1) % 16 = 3 ∨ 3 ^ (2 * k + 1) % 16 = 11 := by
  induction k with
  | zero => left; norm_num
  | succ n ih =>
    have h : 3 ^ (2 * (n + 1) + 1) = 9 * 3 ^ (2 * n + 1) := by ring
    rw [h]
    omega

private theorem gh73x_ordRee_mod {q : ℕ} (hq : q % 16 = 3 ∨ q % 16 = 11) :
    ordRee q % 16 = 8 := by
  show q ^ 3 * (q ^ 3 + 1) * (q - 1) % 16 = 8
  rcases hq with h | h
  · have h1 : q ≡ 3 [MOD 16] := by unfold Nat.ModEq; omega
    have h2 : q - 1 ≡ 2 [MOD 16] := by unfold Nat.ModEq; omega
    have h3 := ((h1.pow 3).mul ((h1.pow 3).add_right 1)).mul h2
    unfold Nat.ModEq at h3
    exact h3.trans (by norm_num)
  · have h1 : q ≡ 11 [MOD 16] := by unfold Nat.ModEq; omega
    have h2 : q - 1 ≡ 10 [MOD 16] := by unfold Nat.ModEq; omega
    have h3 := ((h1.pow 3).mul ((h1.pow 3).add_right 1)).mul h2
    unfold Nat.ModEq at h3
    exact h3.trans (by norm_num)

private theorem gh73x_sixteen_dvd_sq {q : ℕ} (hq : q % 8 = 1 ∨ q % 8 = 7) : 16 ∣ q ^ 2 - 1 := by
  obtain ⟨m, hm⟩ : ∃ m, q = 8 * m + 1 ∨ q = 8 * m + 7 := ⟨q / 8, by omega⟩
  rcases hm with rfl | rfl
  · have h1 : 1 ≤ (8 * m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h : (8 * m + 1) ^ 2 - 1 = 16 * (4 * m ^ 2 + m) := by
      zify [h1]
      ring
    rw [h]
    exact dvd_mul_right _ _
  · have h1 : 1 ≤ (8 * m + 7) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h : (8 * m + 7) ^ 2 - 1 = 16 * (4 * m ^ 2 + 7 * m + 3) := by
      zify [h1]
      ring
    rw [h]
    exact dvd_mul_right _ _

private theorem gh73x_ordBC_two_mul (q : ℕ) :
    ordBC 2 q * Nat.gcd 2 (q - 1) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have hA : Nat.gcd 2 (q - 1) ∣ q ^ 4 - 1 :=
    (Nat.gcd_dvd_right 2 (q - 1)).trans (Nat.sub_one_dvd_pow_sub_one q 4)
  have hB : Nat.gcd 2 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 4 - 1) :=
    hA.trans (dvd_mul_left (q ^ 4 - 1) (q ^ 2 - 1))
  have hdvd : Nat.gcd 2 (q - 1) ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    hB.trans (dvd_mul_left ((q ^ 2 - 1) * (q ^ 4 - 1)) (q ^ 4))
  rw [ordBC, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl, Finset.prod_pair (by norm_num),
    show (2 : ℕ) * 1 = 2 from rfl, show (2 : ℕ) * 2 = 4 from rfl]
  exact Nat.div_mul_cancel hdvd

private theorem gh73x_thirtytwo_dvd_fourth {q : ℕ} (hq : q % 8 = 1 ∨ q % 8 = 7) :
    32 ∣ q ^ 4 - 1 := by
  have hqodd : Odd q := by
    have : q % 2 = 1 := by omega
    exact Nat.odd_iff.mpr this
  have hq1 : 1 ≤ q := by omega
  have h16 := gh73x_sixteen_dvd_sq hq
  have h2 : 2 ∣ q ^ 2 + 1 := by
    obtain ⟨k, hk⟩ : Odd (q ^ 2) := hqodd.pow
    omega
  have h1 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 4 q hq1, Nat.one_le_pow 2 q hq1]
    ring
  rw [h1]
  exact Dvd.dvd.trans (by norm_num : 32 ∣ 16 * 2) (Nat.mul_dvd_mul h16 h2)

private theorem gh73x_dvd_ordBC_two {q : ℕ} (hq : q % 8 = 1 ∨ q % 8 = 7) :
    256 ∣ ordBC 2 q := by
  have hm := gh73x_ordBC_two_mul q
  have hqodd : Odd q := by
    have : q % 2 = 1 := by omega
    exact Nat.odd_iff.mpr this
  have hg : Nat.gcd 2 (q - 1) = 2 := by
    apply Nat.gcd_eq_left
    omega
  have h16 := gh73x_sixteen_dvd_sq hq
  have h32 := gh73x_thirtytwo_dvd_fourth hq
  have h512 : 512 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) :=
    Dvd.dvd.trans (by norm_num : 512 ∣ 16 * 32) (Nat.mul_dvd_mul h16 h32)
  have hd : 512 ∣ ordBC 2 q * Nat.gcd 2 (q - 1) := by
    rw [hm]
    exact Dvd.dvd.mul_left h512 _
  rw [hg] at hd
  omega

private theorem gh73x_factorial_ne {n j : ℕ} (hn : 10 ≤ n) (hn' : n ≤ 11) :
    Nat.factorial n / 2 ≠ 64 * (2 * j + 1) := by
  interval_cases n
  · rw [show Nat.factorial 10 = 3628800 by decide]
    omega
  · rw [show Nat.factorial 11 = 39916800 by decide]
    omega

theorem not_psl4_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : p ^ f % 8 ≠ 1) :
    ¬ LieModel X .PSL 4 p f := by
  intro hL
  have hcard : Nat.card X = ordA 3 (p ^ f) := card_of_lieModel_PSL (by norm_num) hL
  have h128 := gh73x_dvd_ordA_three (q := p ^ f) (hp.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_psu4_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : p ^ f % 8 ≠ 7) :
    ¬ LieModel X .PSU 4 p f := by
  intro hL
  have hcard : Nat.card X = ordTwistedA 3 (p ^ f) := card_of_lieModel_PSU (by norm_num) hp2 hL
  have h128 := gh73x_dvd_ordTwistedA_three (q := p ^ f) (hp.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_psl5_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1))
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 4 = 3) :
    ¬ LieModel X .PSL 5 p f := by
  intro hL
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hcard : Nat.card X = ordA 4 (p ^ f) := card_of_lieModel_PSL (by norm_num) hL
  have h128 := gh73x_dvd_ordA_four (q := p ^ f) (hp.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_psu5_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1))
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : p ^ f % 4 = 1) :
    ¬ LieModel X .PSU 5 p f := by
  intro hL
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hcard : Nat.card X = ordTwistedA 4 (p ^ f) := card_of_lieModel_PSU (by norm_num) hp2 hL
  have h128 := gh73x_dvd_ordTwistedA_four (q := p ^ f) (hp.odd_of_ne_two hp2).pow
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_ree_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1))
    {f : ℕ} : ¬ LieModel X .twistedG2 0 3 f := by
  intro hL
  obtain ⟨k, -, hk⟩ := card_of_lieModel_twistedG2 hL
  have h16 := gh73x_ordRee_mod (gh73x_pow_three_mod k)
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_l28_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ LieModel X .PSL 2 2 3 := by
  intro hL
  have hcard : Nat.card X = ordA 1 (2 ^ 3) := card_of_lieModel_PSL (by norm_num) hL
  have h : ordA 1 (2 ^ 3) = 504 := by decide
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_l216_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ LieModel X .PSL 2 2 4 := by
  intro hL
  have hcard : Nat.card X = ordA 1 (2 ^ 4) := card_of_lieModel_PSL (by norm_num) hL
  have h : ordA 1 (2 ^ 4) = 4080 := by decide
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_alternating_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1))
    {n : ℕ} (hn : 10 ≤ n) (hn' : n ≤ 11) :
    ¬ Nonempty (X ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcard : Nat.card X = Nat.factorial n / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨j, hj⟩ := hc
  exact gh73x_factorial_ne hn hn' (hcard.symm.trans hj)

theorem not_M22_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .M22 := by
  intro h
  have hcard := card_of_isSporadic_M22 h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_M23_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .M23 := by
  intro h
  have hcard := card_of_isSporadic_M23 h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_J1_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .J1 := by
  intro h
  have hcard := card_of_isSporadic_J1 h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_J2_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .J2 := by
  intro h
  have hcard := card_of_isSporadic_J2 h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_J3_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .J3 := by
  intro h
  have hcard := card_of_isSporadic_J3 h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_McL_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .McL := by
  intro h
  have hcard := card_of_isSporadic_McL h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_Ly_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .Ly := by
  intro h
  have hcard := card_of_isSporadic_Ly h
  obtain ⟨j, hj⟩ := hc
  omega

theorem psp4_mod_eight_of_card
    (hc : ∃ j : ℕ, Nat.card X = 64 * (2 * j + 1))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hL : LieModel X .PSp 2 p f) : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
  by_contra hne
  have hcard : Nat.card X = ordBC 2 (p ^ f) := card_of_lieModel_PSp (by norm_num) hp2 hL
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h17 : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7 := by
    have hq2 : p ^ f % 2 = 1 := Nat.odd_iff.mp hodd
    have hne3 : p ^ f % 8 ≠ 3 := fun h => hne (Or.inl h)
    have hne5 : p ^ f % 8 ≠ 5 := fun h => hne (Or.inr h)
    omega
  have h256 := gh73x_dvd_ordBC_two h17
  obtain ⟨j, hj⟩ := hc
  omega

end CFSG.EvenSporadicStandard.HNRecog.GH73