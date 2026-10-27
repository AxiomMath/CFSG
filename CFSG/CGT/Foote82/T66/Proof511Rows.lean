module

public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.CGT.Foote82.Proof511

open CFSG.Blueprint CFSG.GH74
open CFSG.Open (ordA ordTwistedA ordBC ordRee ordSuzuki)

theorem eight_dvd_sq_sub {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring_nf; omega
  rw [h]
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  rw [hj]
  exact ⟨j, by ring⟩

theorem sixteen_dvd_fourth_sub {q : ℕ} (hq : Odd q) : 16 ∣ q ^ 4 - 1 := by
  have hq1 : 1 ≤ q := hq.pos
  have h1 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 4 q hq1, Nat.one_le_pow 2 q hq1]
    ring
  have h2 : 2 ∣ q ^ 2 + 1 := by
    obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
    omega
  rw [h1]
  exact Dvd.dvd.trans (by norm_num : 16 ∣ 8 * 2) (Nat.mul_dvd_mul (eight_dvd_sq_sub hq) h2)

theorem add_one_dvd_cube_add (q : ℕ) : q + 1 ∣ q ^ 3 + 1 :=
  ⟨q ^ 2 - q + 1, by
    have : q ≤ q ^ 2 := by nlinarith
    zify [this]
    ring⟩

private theorem toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  have h : ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) := by push_cast [this]; ring
  rw [h, Int.toNat_natCast]

private theorem toNat_odd {q i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  have h : ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

theorem ordTwistedA_three_mul {q : ℕ} (hq1 : 1 ≤ q) :
    ordTwistedA 3 q * Nat.gcd 4 (q + 1) =
      q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) := by
  rw [ordTwistedA, show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl, Finset.prod_insert
    (by decide), Finset.prod_pair (by norm_num), toNat_even hq1 (by decide),
    toNat_odd (by decide), toNat_even hq1 (by decide),
    show 3 * (3 + 1) / 2 = 6 from rfl, show (3 : ℕ) + 1 = 4 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right (add_one_dvd_cube_add q) _) _) _))

theorem ordA_four_mul (q : ℕ) :
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

theorem ordTwistedA_four_mul {q : ℕ} (hq1 : 1 ≤ q) :
    ordTwistedA 4 q * Nat.gcd 5 (q + 1) =
      q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) := by
  rw [ordTwistedA, show Finset.Icc 2 (4 + 1) = {2, 3, 4, 5} from rfl, Finset.prod_insert
    (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
    toNat_even hq1 (by decide), toNat_odd (by decide), toNat_even hq1 (by decide),
    toNat_odd (by decide), show 4 * (4 + 1) / 2 = 10 from rfl, show (4 : ℕ) + 1 = 5 from rfl]
  exact Nat.div_mul_cancel ((Nat.gcd_dvd_right _ _).trans
    (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right (add_one_dvd_cube_add q) _) _) _))

theorem ordBC_two_mul (q : ℕ) :
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

theorem ordBC_two_ne {q j : ℕ} (hq : Odd q) : ordBC 2 q ≠ 128 * (2 * j + 1) := by
  intro h
  have hq1 : 1 ≤ q := hq.pos
  have hm := ordBC_two_mul q
  have hg : Nat.gcd 2 (q - 1) = 2 := Nat.gcd_eq_left (by obtain ⟨k, rfl⟩ := hq; omega)
  obtain ⟨m, hm8⟩ := eight_dvd_sq_sub hq
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    zify [Nat.one_le_pow 4 q hq1, Nat.one_le_pow 2 q hq1]
    ring
  have h2 : q ^ 2 + 1 = 8 * m + 2 := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq1
    omega
  rw [h, hg, h4, hm8, h2] at hm
  have key : 2 * (2 * j + 1) = q ^ 4 * (m ^ 2 * (4 * m + 1)) := by
    have : 128 * (2 * (2 * j + 1)) = 128 * (q ^ 4 * (m ^ 2 * (4 * m + 1))) := by
      rw [← mul_assoc, show 128 * 2 = 256 by norm_num]
      nlinarith [hm]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | hmo
  ·
    have : 2 * (2 * j + 1) = 4 * (q ^ 4 * (k ^ 2 * (8 * k + 1))) := by rw [key]; ring
    omega
  ·
    have hodd : Odd (q ^ 4 * (m ^ 2 * (4 * m + 1))) :=
      hq.pow.mul (hmo.pow.mul (by rw [Nat.odd_iff]; omega))
    rw [← key] at hodd
    exact (Nat.not_odd_iff_even.mpr ⟨2 * j + 1, by ring⟩) hodd

theorem pow_three_mod_sixteen (k : ℕ) :
    3 ^ (2 * k + 1) % 16 = 3 ∨ 3 ^ (2 * k + 1) % 16 = 11 := by
  induction k with
  | zero => left; norm_num
  | succ n ih =>
    have h : 3 ^ (2 * (n + 1) + 1) = 9 * 3 ^ (2 * n + 1) := by ring
    rw [h]
    omega

theorem ordRee_mod {q : ℕ} (hq : q % 16 = 3 ∨ q % 16 = 11) : ordRee q % 16 = 8 := by
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

variable {X : Type} [Group X]

theorem not_psp4_of_card (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ LieModel X .PSp 2 p f := by
  intro hL
  obtain ⟨j, hj⟩ := hc
  exact ordBC_two_ne (j := j) (hp.odd_of_ne_two hp2).pow
    ((card_of_lieModel_PSp (by norm_num) hp2 hL).symm.trans hj)

theorem not_ree_of_card
    (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) {f : ℕ} : ¬ LieModel X .twistedG2 0 3 f := by
  intro hL
  obtain ⟨k, -, hk⟩ := card_of_lieModel_twistedG2 hL
  have h16 := ordRee_mod (pow_three_mod_sixteen k)
  obtain ⟨j, hj⟩ := hc
  omega

theorem two_dvd_pow_sub_one {q : ℕ} (hq : Odd q) (n : ℕ) : 2 ∣ q ^ n - 1 := by
  obtain ⟨k, hk⟩ : Odd (q ^ n) := hq.pow
  omega

theorem two_dvd_pow_add_one {q : ℕ} (hq : Odd q) (n : ℕ) : 2 ∣ q ^ n + 1 := by
  obtain ⟨k, hk⟩ : Odd (q ^ n) := hq.pow
  omega

theorem not_psl5_of_card (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) {p f : ℕ}
    (hq : Odd (p ^ f)) : ¬ LieModel X .PSL 5 p f := by
  intro hL
  have hcard : Nat.card X = ordA 4 (p ^ f) := card_of_lieModel_PSL (by norm_num) hL
  have hm := ordA_four_mul (p ^ f)
  have hP : 512 ∣ ((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 3 - 1) * (((p ^ f) ^ 4 - 1) *
      ((p ^ f) ^ 5 - 1))) :=
    Dvd.dvd.trans (by norm_num : 512 ∣ 8 * (2 * (16 * 2)))
      (Nat.mul_dvd_mul (eight_dvd_sq_sub hq) (Nat.mul_dvd_mul (two_dvd_pow_sub_one hq 3)
        (Nat.mul_dvd_mul (sixteen_dvd_fourth_sub hq) (two_dvd_pow_sub_one hq 5))))
  have hd : 512 ∣ ordA 4 (p ^ f) * Nat.gcd 5 (p ^ f - 1) := by
    rw [hm]
    exact Dvd.dvd.mul_left hP _
  have hg : Nat.gcd 5 (p ^ f - 1) = 1 ∨ Nat.gcd 5 (p ^ f - 1) = 5 :=
    (Nat.dvd_prime Nat.prime_five).mp (Nat.gcd_dvd_left 5 _)
  obtain ⟨j, hj⟩ := hc
  rcases hg with hg | hg <;> rw [hg] at hd <;> omega

theorem not_psu5_of_card (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) {p f : ℕ}
    (hp2 : p ≠ 2) (hq : Odd (p ^ f)) : ¬ LieModel X .PSU 5 p f := by
  intro hL
  have hcard : Nat.card X = ordTwistedA 4 (p ^ f) := card_of_lieModel_PSU (by norm_num) hp2 hL
  have hm := ordTwistedA_four_mul hq.pos
  have hP : 512 ∣ ((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 3 + 1) * (((p ^ f) ^ 4 - 1) *
      ((p ^ f) ^ 5 + 1))) :=
    Dvd.dvd.trans (by norm_num : 512 ∣ 8 * (2 * (16 * 2)))
      (Nat.mul_dvd_mul (eight_dvd_sq_sub hq) (Nat.mul_dvd_mul (two_dvd_pow_add_one hq 3)
        (Nat.mul_dvd_mul (sixteen_dvd_fourth_sub hq) (two_dvd_pow_add_one hq 5))))
  have hd : 512 ∣ ordTwistedA 4 (p ^ f) * Nat.gcd 5 (p ^ f + 1) := by
    rw [hm]
    exact Dvd.dvd.mul_left hP _
  have hg : Nat.gcd 5 (p ^ f + 1) = 1 ∨ Nat.gcd 5 (p ^ f + 1) = 5 :=
    (Nat.dvd_prime Nat.prime_five).mp (Nat.gcd_dvd_left 5 _)
  obtain ⟨j, hj⟩ := hc
  rcases hg with hg | hg <;> rw [hg] at hd <;> omega

theorem not_psu4_of_card_of_mod_eight (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) {p f : ℕ}
    (hp2 : p ≠ 2) (h8 : p ^ f % 8 = 1) : ¬ LieModel X .PSU 4 p f := by
  intro hL
  have hcard : Nat.card X = ordTwistedA 3 (p ^ f) := card_of_lieModel_PSU (by norm_num) hp2 hL
  obtain ⟨m, hm8⟩ : ∃ m, p ^ f = 8 * m + 1 := ⟨p ^ f / 8, by omega⟩
  have hq : Odd (p ^ f) := ⟨4 * m, by omega⟩
  have hm := ordTwistedA_three_mul hq.pos
  have h16 : 16 ∣ (p ^ f) ^ 2 - 1 := by
    rw [hm8]
    exact ⟨4 * m ^ 2 + m, by
      have : 1 ≤ (8 * m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this]
      ring⟩
  have h32 : 32 ∣ (p ^ f) ^ 4 - 1 := by
    have hq1 : 1 ≤ p ^ f := hq.pos
    have h1 : (p ^ f) ^ 4 - 1 = ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 2 + 1) := by
      zify [Nat.one_le_pow 4 (p ^ f) hq1, Nat.one_le_pow 2 (p ^ f) hq1]
      ring
    rw [h1]
    exact Dvd.dvd.trans (by norm_num : 32 ∣ 16 * 2)
      (Nat.mul_dvd_mul h16 (two_dvd_pow_add_one hq 2))
  have hP : 1024 ∣ ((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) :=
    Dvd.dvd.trans (by norm_num : 1024 ∣ 16 * (2 * 32))
      (Nat.mul_dvd_mul h16 (Nat.mul_dvd_mul (two_dvd_pow_add_one hq 3) h32))
  have hd : 1024 ∣ ordTwistedA 3 (p ^ f) * Nat.gcd 4 (p ^ f + 1) := by
    rw [hm]
    exact Dvd.dvd.mul_left hP _
  have hg : Nat.gcd 4 (p ^ f + 1) = 2 := by
    have h2 : (p ^ f + 1) % 4 = 2 := by omega
    rw [Nat.gcd_rec, h2]
    rfl
  obtain ⟨j, hj⟩ := hc
  rw [hg] at hd
  omega

theorem not_l28_of_card (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) :
    ¬ LieModel X .PSL 2 2 3 := by
  intro hL
  have hcard : Nat.card X = ordA 1 (2 ^ 3) := card_of_lieModel_PSL (by norm_num) hL
  have h : ordA 1 (2 ^ 3) = 504 := by decide
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_l216_of_card (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) :
    ¬ LieModel X .PSL 2 2 4 := by
  intro hL
  have hcard : Nat.card X = ordA 1 (2 ^ 4) := card_of_lieModel_PSL (by norm_num) hL
  have h : ordA 1 (2 ^ 4) = 4080 := by decide
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_l34_of_card (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) :
    ¬ LieModel X .PSL 3 2 2 := by
  intro hL
  have hcard : Nat.card X = ordA 2 (2 ^ 2) := card_of_lieModel_PSL (by norm_num) hL
  have h : ordA 2 (2 ^ 2) = 20160 := by decide
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_sz8_of_card
    (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) : ¬ LieModel X .twistedB2 0 2 3 := by
  intro hL
  have hcard := card_of_lieModel_twistedB2 hL
  have h : ordSuzuki 8 = 29120 := by decide
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_alternating_of_card (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) {n : ℕ}
    (hn : 8 ≤ n) (hn' : n ≤ 9) : ¬ Nonempty (X ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcard : Nat.card X = Nat.factorial n / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨j, hj⟩ := hc
  interval_cases n
  · rw [show Nat.factorial 8 = 40320 by decide] at hcard
    omega
  · rw [show Nat.factorial 9 = 362880 by decide] at hcard
    omega

theorem not_M12_of_card
    (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .M12 := by
  intro h
  have hcard := card_of_isSporadic_M12 h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_J1_of_card
    (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .J1 := by
  intro h
  have hcard := card_of_isSporadic_J1 h
  obtain ⟨j, hj⟩ := hc
  omega

theorem not_Ly_of_card
    (hc : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)) : ¬ NativeSporadic.IsSporadic X .Ly := by
  intro h
  have hcard := card_of_isSporadic_Ly h
  obtain ⟨j, hj⟩ := hc
  omega

end CFSG.CGT.Foote82.Proof511
