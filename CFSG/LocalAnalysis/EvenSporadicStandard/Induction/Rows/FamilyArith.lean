module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Open

theorem two_pow_le_succ_of_dvd_sq_sub_one {q a : ℕ} (hq : Odd q) (hq1 : 1 < q) (ha : 1 ≤ a)
    (h : 2 ^ (a + 1) ∣ q ^ 2 - 1) : 2 ^ a ≤ q + 1 := by
  obtain ⟨m, rfl⟩ := hq
  have hm0 : 0 < m := by omega
  have e : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  rw [e] at h
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h4 : 2 ^ (b + 1 + 1) = 4 * 2 ^ b := by simp [pow_succ]; ring
  rw [h4] at h
  have h5 : 2 ^ b ∣ m * (m + 1) := (Nat.mul_dvd_mul_iff_left (by norm_num)).1 h
  have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by simp [pow_succ]; ring
  rcases Nat.even_or_odd m with hm | hm
  · have : Nat.Coprime (2 ^ b) (m + 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 (by simpa [Nat.odd_add_one] using hm))
    have h6 : 2 ^ b ∣ m := this.dvd_of_dvd_mul_right h5
    have := Nat.le_of_dvd hm0 h6
    omega
  · have : Nat.Coprime (2 ^ b) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
    have h6 : 2 ^ b ∣ m + 1 := this.dvd_of_dvd_mul_left h5
    have := Nat.le_of_dvd (by omega) h6
    omega

theorem cube_sub_mono {q P : ℤ} (hP : 2 ≤ P) (h : P ≤ q) : P * (P ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
  nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h),
    mul_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℤ) ≤ P)]

theorem not_psl2_g2 {n : ℕ} (hn : 1 ≤ n) {q : ℕ} (hq : Odd q) (hq1 : 1 < q)
    (h : q * (q ^ 2 - 1) = 2 * ((2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) : False := by
  set Q : ℕ := 2 ^ n with hQ
  have hQ2 : 2 ≤ Q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hdvd : 2 ^ (6 * n + 1) ∣ q * (q ^ 2 - 1) := by
    rw [h]
    have : Q ^ 6 = 2 ^ (6 * n) := by rw [hQ, ← pow_mul]; ring_nf
    rw [this]
    exact ⟨((2 ^ (6 * n) - 1) * (Q ^ 2 - 1)), by ring⟩
  have hcop : Nat.Coprime (2 ^ (6 * n + 1)) q :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hq)
  have h2 : 2 ^ (6 * n + 1) ∣ q ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdvd
  have h3 := two_pow_le_succ_of_dvd_sq_sub_one hq hq1 (by omega) h2
  have hX : Q ^ 6 = 2 ^ (6 * n) := by rw [hQ, ← pow_mul]; ring_nf
  rw [← hX] at h3
  have hQ4 : (4 : ℕ) ≤ Q ^ 2 := by nlinarith
  have hq3 : 3 ≤ q := by
    obtain ⟨m, rfl⟩ := hq
    omega
  have hq2 : (q : ℤ) ^ 2 ≥ 1 := by nlinarith
  have hQ6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hQ2' : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsub1 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have hsub2 : (((Q ^ 6) - 1 : ℕ) : ℤ) = (Q : ℤ) ^ 6 - 1 := by
    rw [Nat.cast_sub hQ6]; push_cast; ring
  have hsub3 : (((Q ^ 2) - 1 : ℕ) : ℤ) = (Q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hQ2']; push_cast; ring
  have hz : (q : ℤ) * ((q : ℤ) ^ 2 - 1) =
      2 * ((Q : ℤ) ^ 6 * ((Q : ℤ) ^ 6 - 1) * ((Q : ℤ) ^ 2 - 1)) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    simp only [Nat.cast_mul, hsub1, hsub2, hsub3] at this
    push_cast at this
    linarith
  have hP : ((Q : ℤ) ^ 6 - 1) ≤ q := by
    have : ((Q ^ 6 : ℕ) : ℤ) ≤ (q : ℤ) + 1 := by exact_mod_cast h3
    push_cast at this
    linarith
  have hQz : (2 : ℤ) ≤ Q := by exact_mod_cast hQ2
  have hP2 : (2 : ℤ) ≤ (Q : ℤ) ^ 6 - 1 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hQz 6]
  have hmono := cube_sub_mono hP2 hP
  have hQ4z : (Q : ℤ) ^ 4 > 2 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 2) hQz 4]
  have key : ((Q : ℤ) ^ 6 - 1) * (((Q : ℤ) ^ 6 - 1) ^ 2 - 1) >
      2 * ((Q : ℤ) ^ 6 * ((Q : ℤ) ^ 6 - 1) * ((Q : ℤ) ^ 2 - 1)) := by
    have hpos : (0 : ℤ) < (Q : ℤ) ^ 6 - 1 := by linarith
    have : ((Q : ℤ) ^ 6 - 1) ^ 2 - 1 > 2 * ((Q : ℤ) ^ 6 * ((Q : ℤ) ^ 2 - 1)) := by
      have hQ2z : (0 : ℤ) < (Q : ℤ) ^ 2 := by positivity
      nlinarith [mul_pos hQ2z hQ2z, mul_pos (mul_pos hQ2z hQ2z) hQ2z]
    nlinarith [mul_pos hpos (sub_pos.2 this)]
  linarith

theorem ordA_two (Q : ℕ) : ordA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) / Nat.gcd 3 (Q - 1) := by
  unfold ordA
  have : ∏ i ∈ Finset.Icc 2 3, (Q ^ i - 1) = (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide]
    simp
  simp [this]

theorem not_psl2_l3 {n : ℕ} (hn : 2 ≤ n) {q d : ℕ} (hq : Odd q) (hq1 : 1 < q) (hd : Odd d)
    (hd1 : 1 ≤ d)
    (h : q * (q ^ 2 - 1) * d = 2 * ((2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))) :
    False := by
  set Q : ℕ := 2 ^ n with hQ
  have hQ4 : 4 ≤ Q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hX : Q ^ 3 = 2 ^ (3 * n) := by rw [hQ, ← pow_mul]; ring_nf
  have hdvd : 2 ^ (3 * n + 1) ∣ q * (q ^ 2 - 1) * d := by
    rw [h, hX]
    exact ⟨((Q ^ 2 - 1) * (2 ^ (3 * n) - 1)), by ring⟩
  have hcopd : Nat.Coprime (2 ^ (3 * n + 1)) d := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hd)
  have hdvd' : 2 ^ (3 * n + 1) ∣ q * (q ^ 2 - 1) := hcopd.dvd_of_dvd_mul_right hdvd
  have hcop : Nat.Coprime (2 ^ (3 * n + 1)) q :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hq)
  have h2 : 2 ^ (3 * n + 1) ∣ q ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hdvd'
  have h3 := two_pow_le_succ_of_dvd_sq_sub_one hq hq1 (by omega) h2
  rw [← hX] at h3
  have hq3 : 3 ≤ q := by
    obtain ⟨m, rfl⟩ := hq
    omega
  have hQ3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hQ2' : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsub1 : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have hsub2 : (((Q ^ 3) - 1 : ℕ) : ℤ) = (Q : ℤ) ^ 3 - 1 := by
    rw [Nat.cast_sub hQ3]; push_cast; ring
  have hsub3 : (((Q ^ 2) - 1 : ℕ) : ℤ) = (Q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hQ2']; push_cast; ring
  have hz : (q : ℤ) * ((q : ℤ) ^ 2 - 1) * d =
      2 * ((Q : ℤ) ^ 3 * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 3 - 1))) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    simp only [Nat.cast_mul, hsub1, hsub2, hsub3] at this
    push_cast at this
    linarith
  have hP : ((Q : ℤ) ^ 3 - 1) ≤ q := by
    have : ((Q ^ 3 : ℕ) : ℤ) ≤ (q : ℤ) + 1 := by exact_mod_cast h3
    push_cast at this
    linarith
  have hQz : (4 : ℤ) ≤ Q := by exact_mod_cast hQ4
  have hP2 : (2 : ℤ) ≤ (Q : ℤ) ^ 3 - 1 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 4) hQz 3]
  have hmono := cube_sub_mono hP2 hP
  have hd1z : (1 : ℤ) ≤ d := by exact_mod_cast hd1
  have hpos : (0 : ℤ) < (Q : ℤ) ^ 3 - 1 := by linarith
  have hQ2z : (0 : ℤ) < (Q : ℤ) ^ 2 := by positivity
  have hQ3z : (0 : ℤ) < (Q : ℤ) ^ 3 := by positivity
  have hXY : (Q : ℤ) ^ 3 > 2 * (Q : ℤ) ^ 2 := by
    have : (Q : ℤ) ^ 3 = (Q : ℤ) * (Q : ℤ) ^ 2 := by ring
    rw [this]
    nlinarith
  have hineq : ((Q : ℤ) ^ 3 - 1) ^ 2 - 1 > 2 * ((Q : ℤ) ^ 3 * ((Q : ℤ) ^ 2 - 1)) := by
    have e : (((Q : ℤ) ^ 3 - 1) ^ 2 - 1) - 2 * ((Q : ℤ) ^ 3 * ((Q : ℤ) ^ 2 - 1)) =
        (Q : ℤ) ^ 3 * ((Q : ℤ) ^ 3 - 2 * (Q : ℤ) ^ 2) := by ring
    have : 0 < (Q : ℤ) ^ 3 * ((Q : ℤ) ^ 3 - 2 * (Q : ℤ) ^ 2) := mul_pos hQ3z (by linarith)
    linarith
  have key : ((Q : ℤ) ^ 3 - 1) * (((Q : ℤ) ^ 3 - 1) ^ 2 - 1) >
      2 * ((Q : ℤ) ^ 3 * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 3 - 1))) := by
    have e : ((Q : ℤ) ^ 3 - 1) * (((Q : ℤ) ^ 3 - 1) ^ 2 - 1) -
        2 * ((Q : ℤ) ^ 3 * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 3 - 1))) =
        ((Q : ℤ) ^ 3 - 1) *
          ((((Q : ℤ) ^ 3 - 1) ^ 2 - 1) - 2 * ((Q : ℤ) ^ 3 * ((Q : ℤ) ^ 2 - 1))) := by
      ring
    have : 0 < ((Q : ℤ) ^ 3 - 1) * ((((Q : ℤ) ^ 3 - 1) ^ 2 - 1) -
        2 * ((Q : ℤ) ^ 3 * ((Q : ℤ) ^ 2 - 1))) := mul_pos hpos (by linarith)
    linarith
  have hbig : (Q : ℤ) ^ 3 - 1 > 0 := hpos
  have hge : ((Q : ℤ) ^ 3 - 1) * (((Q : ℤ) ^ 3 - 1) ^ 2 - 1) ≤ (q : ℤ) * ((q : ℤ) ^ 2 - 1) * d := by
    have hnn : (0 : ℤ) ≤ ((Q : ℤ) ^ 3 - 1) * (((Q : ℤ) ^ 3 - 1) ^ 2 - 1) := by
      have : (0 : ℤ) ≤ ((Q : ℤ) ^ 3 - 1) ^ 2 - 1 := by nlinarith
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hd1z hnn]
  linarith


theorem not_psl2_ordA {n : ℕ} (hn : 2 ≤ n) {q : ℕ} (hq : Odd q) (hq1 : 1 < q) :
    q * (q ^ 2 - 1) ≠ 2 * ordA 2 (2 ^ n) := by
  intro h
  set Q : ℕ := 2 ^ n with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  set d : ℕ := Nat.gcd 3 (Q - 1) with hd
  have hd3 : d ∣ 3 := Nat.gcd_dvd_left _ _
  have hdodd : Odd d := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h1 | h1
    · rw [h1]; exact odd_one
    · rw [h1]; exact ⟨1, rfl⟩
  have hdpos : 1 ≤ d := hdodd.pos
  have hdvd : d ∣ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
    exact (Nat.gcd_dvd_right 3 (Q - 1)).trans (Nat.sub_one_dvd_pow_sub_one Q 2)
  have hA : d * ordA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
    rw [ordA_two]
    exact Nat.mul_div_cancel' hdvd
  refine not_psl2_l3 hn hq hq1 hdodd hdpos ?_
  rw [mul_comm (q * (q ^ 2 - 1)) d, h, ← hA]
  ring

theorem notExc_of_card_family {X : Type} [Group X] {N : ℕ} (hN : Nat.card X = N)
    (hbig : 2520 < N) (hpsl : ∀ q : ℕ, Odd q → 1 < q → q * (q ^ 2 - 1) ≠ 2 * N) :
    ¬ Nonempty (X ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel X .PSL 2 p f := by
  constructor
  · rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [hN, card_alternatingGroup_seven] at h
    omega
  · rintro ⟨p, f, hp, hp2, hm⟩
    have h := two_mul_card_of_lieModel_psl_two hp hp2 hm
    rw [hN] at h
    have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hq1 : 1 < p ^ f := by
      rcases Nat.lt_or_ge 1 (p ^ f) with h1 | h1
      · exact h1
      · exfalso
        have : p ^ f = 1 := by
          obtain ⟨m, hm⟩ := hq
          omega
        rw [this] at h
        omega
    exact hpsl (p ^ f) hq hq1 h.symm

theorem ordG2_gt (n : ℕ) (hn : 1 ≤ n) : 2520 < ordG2 (2 ^ n) := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  unfold ordG2
  have h6 : 64 ≤ (2 ^ n) ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left h2 6
  have h4 : 3 ≤ (2 ^ n) ^ 2 - 1 := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  have h5 : 63 ≤ (2 ^ n) ^ 6 - 1 := by omega
  calc 2520 < 64 * 63 * 3 := by norm_num
    _ ≤ (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) := by gcongr

theorem ordA_gt (n : ℕ) (hn : 2 ≤ n) : 2520 < ordA 2 (2 ^ n) := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [ordA_two]
  have hd3 : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hdpos : 0 < Nat.gcd 3 (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hnum : 60480 ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    have h1 : 64 ≤ (2 ^ n) ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h4 3
    have h2 : 15 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have h3 : 63 ≤ (2 ^ n) ^ 3 - 1 := by omega
    calc 60480 = 64 * (15 * 63) / 1 := by norm_num
      _ ≤ _ := by
        have : 64 * (15 * 63) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
          gcongr
        omega
  calc 2520 < 60480 / 3 := by norm_num
    _ ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) / 3 := Nat.div_le_div_right hnum
    _ ≤ _ := Nat.div_le_div_left hd3 hdpos

theorem notExc_of_card_g2 {n : ℕ} (hn : 1 ≤ n) {X : Type} [Group X]
    (h : Nat.card X = ordG2 (2 ^ n)) :
    ¬ Nonempty (X ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel X .PSL 2 p f :=
  notExc_of_card_family h (ordG2_gt n hn) fun q hq hq1 hh => not_psl2_g2 hn hq hq1 (by
    simpa [ordG2] using hh)

theorem notExc_of_card_l3 {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    (h : Nat.card X = ordA 2 (2 ^ n)) :
    ¬ Nonempty (X ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel X .PSL 2 p f :=
  notExc_of_card_family h (ordA_gt n hn) fun _ hq hq1 => not_psl2_ordA hn hq hq1

theorem padicValNat_ordG2 {n : ℕ} (hn : 1 ≤ n) : padicValNat 2 (ordG2 (2 ^ n)) = 6 * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h6 : 2 ∣ (2 ^ n) ^ 6 := dvd_pow h2n (by norm_num)
  have h6' : 1 ≤ (2 ^ n) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h22 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow h2n (by norm_num)
  have h22' : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ho6 : ¬ 2 ∣ (2 ^ n) ^ 6 - 1 := by omega
  have ho2 : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by omega
  have hne6 : (2 ^ n) ^ 6 - 1 ≠ 0 := by
    intro h
    have : (2 ^ n) ^ 6 = 1 := by omega
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 2 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left h2 6
    omega
  have hne2 : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    intro h
    have : (2 ^ n) ^ 2 = 1 := by omega
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 2 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  unfold ordG2
  rw [padicValNat.mul (by positivity) hne2, padicValNat.mul (by positivity) hne6,
    padicValNat.eq_zero_of_not_dvd ho6, padicValNat.eq_zero_of_not_dvd ho2, ← pow_mul,
    padicValNat.prime_pow]
  ring

theorem padicValNat_card_co1 : padicValNat 2 4157776806543360000 = 21 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (4157776806543360000 : ℕ) = 2 ^ 21 * 1982582476875 := by norm_num
  rw [h, padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem ordG2_ne_card_co1 {n : ℕ} (hn : 1 ≤ n) : ordG2 (2 ^ n) ≠ 4157776806543360000 := by
  intro h
  have := padicValNat_ordG2 hn
  rw [h, padicValNat_card_co1] at this
  omega

end CFSG.EvenSporadicStandard.Induction
