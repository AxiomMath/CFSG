module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110n

open CFSG.Open Finset
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula coprime_of_dvd_sub_one
  coprime_of_dvd_add_one coprime_of_dvd_pow_sub_one coprime_of_dvd_pow_add_one sub_one_dvd_sq_sub_one
  add_one_dvd_sq_sub_one)

section Order

@[expose] def d4TwoPrimePowers_d4n : List ℕ :=
  [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 3, 9, 27, 81, 243, 5, 25, 7]

theorem prime_power_dvd_d4Two_d4n {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (h : q ^ e ∣ 174182400) : q ∈ d4TwoPrimePowers_d4n ∧ e ≤ 12 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ 174182400 :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h4 : p ∈ ([2, 3, 5, 7] : List ℕ) := by
    have hF : (174182400 : ℕ) = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 := by norm_num
    rw [hF] at hpF
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h1 | h1
    · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hpp).1 h2 with h3 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h3))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1
            (hpp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1
          (hpp.dvd_of_dvd_pow h2))))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h1)))
  have hm : p ^ (k * e) ∣ 174182400 := by rwa [pow_mul]
  have hlt : k * e < 28 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 28 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ 174182400 := Nat.le_of_dvd (by norm_num) hm
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ 174182400 := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ ([2, 3, 5, 7] : List ℕ), ∀ m < 28, p ^ m ∣ 174182400 → m ≤ 12 := by
    decide +kernel
  have key2 : ∀ p ∈ ([2, 3, 5, 7] : List ℕ), ∀ m < 28, 1 ≤ m → p ^ m ∣ 174182400 →
      p ^ m ∈ d4TwoPrimePowers_d4n := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  refine ⟨key2 p h4 k (by omega) hk hkF, ?_⟩
  have := key p h4 (k * e) hlt hm
  have h7 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

theorem gen_bound_d4n {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (hG : Nat.Coprime q G)
    (hmul : G * N = q ^ e * R) (hN : N = 174182400) : q ∈ d4TwoPrimePowers_d4n ∧ e ≤ 12 := by
  have h1 : q ^ e ∣ G * 174182400 := ⟨R, by rw [← hN, hmul]⟩
  exact prime_power_dvd_d4Two_d4n hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

theorem gen_bound'_d4n {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (hmul : N = q ^ e * R)
    (hN : N = 174182400) : q ∈ d4TwoPrimePowers_d4n ∧ e ≤ 12 :=
  gen_bound_d4n hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

theorem orderA_ne_d4n {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) : orderA n q ≠ 174182400 := by
  intro h
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq20, he⟩ := gen_bound_d4n hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 15 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4] : List ℕ), ∀ q ∈ d4TwoPrimePowers_d4n,
      orderA n q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid n (by simp; omega) q hq20 h

theorem orderTwistedA_ne_d4n {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) :
    orderTwistedA n q ≠ 174182400 := by
  intro h
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hfac : q + 1 ∣ (fun i => if Even i then q ^ i - 1 else q ^ i + 1) 2 := by
    show q + 1 ∣ (if Even 2 then q ^ 2 - 1 else q ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one q (by omega)
  have hGd : Nat.gcd (n + 1) (q + 1) ∣ q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q + 1) * orderTwistedA n q = q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq20, he⟩ := gen_bound_d4n hq he1 (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 15 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4] : List ℕ), ∀ q ∈ d4TwoPrimePowers_d4n,
      orderTwistedA n q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid n (by simp; omega) q hq20 h

theorem orderBC_ne_d4n {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) : orderBC n q ≠ 174182400 := by
  intro h
  have hq2 := hq.two_le
  have hmem : 1 ∈ Icc 1 n := by simp; omega
  have hfac : q - 1 ∣ (fun i => q ^ (2 * i) - 1) 1 := by
    show q - 1 ∣ q ^ (2 * 1) - 1
    exact Nat.sub_one_dvd_pow_sub_one q (2 * 1)
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem)) _
  have hmul : Nat.gcd 2 (q - 1) * orderBC n q = q ^ (n * n) * ∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1) :=
    Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * n := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨hq20, he⟩ := gen_bound_d4n hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn3 : n ≤ 3 := by
    by_contra hc
    push Not at hc
    nlinarith
  have grid : ∀ n ∈ ([1, 2, 3] : List ℕ), ∀ q ∈ d4TwoPrimePowers_d4n,
      orderBC n q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid n (by simp; omega) q hq20 h

theorem orderD_eq_d4n {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) (h : orderD n q = 174182400) :
    n = 4 ∧ q = 2 := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n - 1) ∣ q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n - 1) * orderD n q = q ^ (n * (n - 1)) * ((q ^ n - 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by ring
    unfold orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n - 1) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  obtain ⟨hq20, he⟩ := gen_bound_d4n hq he1
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ d4TwoPrimePowers_d4n, orderD 4 q = 174182400 → q = 2 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact ⟨rfl, grid q hq20 h⟩

theorem orderTwistedD_ne_d4n {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    orderTwistedD n q ≠ 174182400 := by
  intro h
  have hq2 := hq.two_le
  have hGd : Nat.gcd 4 (q ^ n + 1) ∣ q ^ (n * (n - 1)) * ((q ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (q ^ n + 1) * orderTwistedD n q = q ^ (n * (n - 1)) * ((q ^ n + 1) *
      ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by
    have h1 : q ^ (n * (n - 1)) * (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) =
        q ^ (n * (n - 1)) * ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) := by ring
    unfold orderTwistedD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n - 1) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  obtain ⟨hq20, he⟩ := gen_bound_d4n hq he1
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ d4TwoPrimePowers_d4n, orderTwistedD 4 q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact grid q hq20 h

theorem orderE6_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderE6 q ≠ 174182400 := by
  intro h
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q - 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (sub_one_dvd_sq_sub_one q)) _) _
  have hmul : Nat.gcd 3 (q - 1) * orderE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE6
    rw [show q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := gen_bound_d4n hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderTwistedE6_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderTwistedE6 q ≠ 174182400 := by
  intro h
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q + 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (add_one_dvd_sq_sub_one q (by omega))) _) _
  have hmul : Nat.gcd 3 (q + 1) * orderTwistedE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderTwistedE6
    rw [show q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1)) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := gen_bound_d4n hq (by norm_num)
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderE7_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderE7 q ≠ 174182400 := by
  intro h
  have hq2 := hq.two_le
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (sub_one_dvd_sq_sub_one q)) _) _
  have hmul : Nat.gcd 2 (q - 1) * orderE7 q = q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE7
    rw [show q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1)) = q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := gen_bound_d4n hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul h
  omega

theorem orderE8_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderE8 q ≠ 174182400 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound'_d4n (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) *
    (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

theorem orderF4_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderF4 q ≠ 174182400 := by
  intro h
  obtain ⟨-, he⟩ := gen_bound'_d4n (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) h
  omega

theorem orderG2_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderG2 q ≠ 174182400 := by
  intro h
  obtain ⟨hq20, -⟩ := gen_bound'_d4n (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderG2; ring) h
  have grid : ∀ q ∈ d4TwoPrimePowers_d4n, orderG2 q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid q hq20 h

theorem orderTrialityD4_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderTrialityD4 q ≠ 174182400 := by
  intro h
  obtain ⟨hq20, -⟩ := gen_bound'_d4n (e := 12)
    (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderTrialityD4; ring) h
  have grid : ∀ q ∈ d4TwoPrimePowers_d4n, orderTrialityD4 q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid q hq20 h

theorem orderSuzuki_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderSuzuki q ≠ 174182400 := by
  intro h
  obtain ⟨hq20, -⟩ := gen_bound'_d4n (e := 2) (R := (q ^ 2 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderSuzuki; ring) h
  have grid : ∀ q ∈ d4TwoPrimePowers_d4n, orderSuzuki q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid q hq20 h

theorem orderRee_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderRee q ≠ 174182400 := by
  intro h
  obtain ⟨hq20, -⟩ := gen_bound'_d4n (e := 3) (R := (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderRee; ring) h
  have grid : ∀ q ∈ d4TwoPrimePowers_d4n, orderRee q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid q hq20 h

theorem orderTwistedF4_ne_d4n {q : ℕ} (hq : IsPrimePow q) : orderTwistedF4 q ≠ 174182400 := by
  intro h
  obtain ⟨hq20, -⟩ := gen_bound'_d4n (e := 12)
    (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderTwistedF4; ring) h
  have grid : ∀ q ∈ d4TwoPrimePowers_d4n, orderTwistedF4 q ≠ 174182400 := by
    unfold d4TwoPrimePowers_d4n
    decide +kernel
  exact grid q hq20 h

theorem orderTits_ne_d4n : orderTits ≠ 174182400 := by
  unfold orderTits
  norm_num

theorem eq_D4_two_of_lieOrderFormula_d4n {d : TauCeti.LieTypeIndex} (hd : d.Valid)
    (h : lieOrderFormula d = 174182400) : ∃ q : TauCeti.PrimePower, d = .D 4 q ∧ q.card = 2 := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q => exact (orderA_ne_d4n hs.1 q.isPrimePow_card h).elim
  | twistedA n q => exact (orderTwistedA_ne_d4n (by omega : 1 ≤ n) q.isPrimePow_card h).elim
  | B n q => exact (orderBC_ne_d4n (by omega : 1 ≤ n) q.isPrimePow_card h).elim
  | C n q => exact (orderBC_ne_d4n (by omega : 1 ≤ n) q.isPrimePow_card h).elim
  | D n q =>
    obtain ⟨rfl, hq⟩ := orderD_eq_d4n hs q.isPrimePow_card h
    exact ⟨q, rfl, hq⟩
  | twistedD n q => exact (orderTwistedD_ne_d4n hs q.isPrimePow_card h).elim
  | E6 q => exact (orderE6_ne_d4n q.isPrimePow_card h).elim
  | E7 q => exact (orderE7_ne_d4n q.isPrimePow_card h).elim
  | E8 q => exact (orderE8_ne_d4n q.isPrimePow_card h).elim
  | F4 q => exact (orderF4_ne_d4n q.isPrimePow_card h).elim
  | G2 q => exact (orderG2_ne_d4n q.isPrimePow_card h).elim
  | twistedE6 q => exact (orderTwistedE6_ne_d4n q.isPrimePow_card h).elim
  | trialityD4 q => exact (orderTrialityD4_ne_d4n q.isPrimePow_card h).elim
  | suzuki m => exact (orderSuzuki_ne_d4n (Nat.prime_two.isPrimePow.pow (by omega)) h).elim
  | reeG2 m => exact (orderRee_ne_d4n (Nat.prime_three.isPrimePow.pow (by omega)) h).elim
  | reeF4 m => exact (orderTwistedF4_ne_d4n (Nat.prime_two.isPrimePow.pow (by omega)) h).elim
  | tits => exact (orderTits_ne_d4n h).elim

end Order

section Subfield

@[expose] def phi5_d4n (x : ℕ) : ℕ := x ^ 4 + x ^ 3 + x ^ 2 + x + 1

@[expose] def phi10_d4n (x : ℕ) : ℕ := x ^ 4 + x ^ 2 + 1 - (x ^ 3 + x)

@[expose] def theta_d4n (y : ℕ) : ℕ := y ^ 8 + y ^ 5 + y ^ 3 + 1 - (y ^ 7 + y ^ 4 + y)

theorem pow_five_sub_one_d4n (x : ℕ) : x ^ 5 - 1 = (x - 1) * phi5_d4n x := by
  unfold phi5_d4n
  rcases x with _ | x
  · simp
  · have h : (x + 1) ^ 5 = x * ((x + 1) ^ 4 + (x + 1) ^ 3 + (x + 1) ^ 2 + (x + 1) + 1) + 1 := by ring
    rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem phi10_le_d4n (x : ℕ) : x ^ 3 + x ≤ x ^ 4 + x ^ 2 + 1 := by
  rcases x with _ | x
  · simp
  · have h1 : (x + 1) ^ 3 ≤ (x + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : x + 1 ≤ (x + 1) ^ 2 := by nlinarith
    omega

theorem pow_five_add_one_d4n (x : ℕ) : x ^ 5 + 1 = (x + 1) * phi10_d4n x := by
  unfold phi10_d4n
  have h := phi10_le_d4n x
  zify [h]
  ring

theorem theta_le_d4n (y : ℕ) : y ^ 7 + y ^ 4 + y ≤ y ^ 8 + y ^ 5 + y ^ 3 + 1 := by
  rcases Nat.lt_or_ge y 2 with hy | hy
  · interval_cases y <;> simp
  · have h7 : 2 * y ^ 7 ≤ y ^ 8 := by
      rw [pow_succ y 7]
      nlinarith [Nat.zero_le (y ^ 7)]
    have h3 : y ^ 4 ≤ y ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : y ≤ y ^ 3 := Nat.le_self_pow (by norm_num) _
    omega

theorem trialityFactor_d4n (y : ℕ) : y ^ 10 + y ^ 5 + 1 = (y ^ 2 + y + 1) * theta_d4n y := by
  unfold theta_d4n
  have h := theta_le_d4n y
  zify [h]
  ring

theorem not_three_dvd_phi5_d4n (x : ℕ) : ¬ 3 ∣ phi5_d4n x := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold phi5_d4n
  push_cast
  generalize (x : ZMod 3) = y
  revert y
  decide

theorem not_two_dvd_phi5_d4n (x : ℕ) : ¬ 2 ∣ phi5_d4n x := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold phi5_d4n
  push_cast
  generalize (x : ZMod 2) = y
  revert y
  decide

theorem not_three_dvd_phi10_d4n (x : ℕ) : ¬ 3 ∣ phi10_d4n x := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold phi10_d4n
  rw [Nat.cast_sub (phi10_le_d4n x)]
  push_cast
  generalize (x : ZMod 3) = y
  revert y
  decide

theorem not_three_dvd_theta_d4n (y : ℕ) : ¬ 3 ∣ theta_d4n y := by
  rw [← ZMod.natCast_eq_zero_iff]
  unfold theta_d4n
  rw [Nat.cast_sub (theta_le_d4n y)]
  push_cast
  generalize (y : ZMod 3) = z
  revert z
  decide

theorem not_three_dvd_mul_d4n {a b : ℕ} (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) : ¬ 3 ∣ a * b := fun h =>
  ((Nat.Prime.dvd_mul Nat.prime_three).1 h).elim ha hb

theorem not_three_dvd_pow_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) (k : ℕ) : ¬ 3 ∣ Q ^ k := fun h =>
  hQ (Nat.prime_three.dvd_of_dvd_pow h)

theorem pow_pow_five_sub_one_d4n (x d : ℕ) : (x ^ 5) ^ d - 1 = (x ^ d - 1) * phi5_d4n (x ^ d) := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact pow_five_sub_one_d4n _

theorem pow_pow_five_add_one_d4n (x d : ℕ) : (x ^ 5) ^ d + 1 = (x ^ d + 1) * phi10_d4n (x ^ d) := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact pow_five_add_one_d4n _

theorem gcd_three_pow_five_sub_one_d4n (Q : ℕ) : Nat.gcd 3 (Q ^ 5 - 1) = Nat.gcd 3 (Q - 1) := by
  rw [pow_five_sub_one_d4n]
  exact Nat.gcd_mul_left_right_of_gcd_eq_one
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_three_dvd_phi5_d4n Q))

theorem gcd_three_pow_five_add_one_d4n (Q : ℕ) : Nat.gcd 3 (Q ^ 5 + 1) = Nat.gcd 3 (Q + 1) := by
  rw [pow_five_add_one_d4n]
  exact Nat.gcd_mul_left_right_of_gcd_eq_one
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_three_dvd_phi10_d4n Q))

theorem gcd_two_pow_five_sub_one_d4n (Q : ℕ) : Nat.gcd 2 (Q ^ 5 - 1) = Nat.gcd 2 (Q - 1) := by
  rw [pow_five_sub_one_d4n]
  exact Nat.gcd_mul_left_right_of_gcd_eq_one
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (not_two_dvd_phi5_d4n Q))

theorem orderG2_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderG2 (Q ^ 5) = orderG2 Q * R ∧ ¬ 3 ∣ R := by
  refine ⟨Q ^ 24 * phi5_d4n (Q ^ 6) * phi5_d4n (Q ^ 2), ?_, ?_⟩
  · unfold orderG2
    rw [pow_pow_five_sub_one_d4n Q 6, pow_pow_five_sub_one_d4n Q 2]
    ring
  · exact not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_pow_d4n hQ _)
      (not_three_dvd_phi5_d4n _)) (not_three_dvd_phi5_d4n _)

theorem orderF4_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderF4 (Q ^ 5) = orderF4 Q * R ∧ ¬ 3 ∣ R := by
  refine ⟨Q ^ 96 * phi5_d4n (Q ^ 12) * phi5_d4n (Q ^ 8) * phi5_d4n (Q ^ 6) * phi5_d4n (Q ^ 2),
    ?_, ?_⟩
  · unfold orderF4
    rw [pow_pow_five_sub_one_d4n Q 12, pow_pow_five_sub_one_d4n Q 8, pow_pow_five_sub_one_d4n Q 6,
      pow_pow_five_sub_one_d4n Q 2]
    ring
  · refine not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_pow_d4n hQ _) ?_) ?_) ?_) ?_ <;>
      exact not_three_dvd_phi5_d4n _

theorem orderE8_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderE8 (Q ^ 5) = orderE8 Q * R ∧ ¬ 3 ∣ R := by
  refine ⟨Q ^ 480 * phi5_d4n (Q ^ 30) * phi5_d4n (Q ^ 24) * phi5_d4n (Q ^ 20) *
    phi5_d4n (Q ^ 18) * phi5_d4n (Q ^ 14) * phi5_d4n (Q ^ 12) * phi5_d4n (Q ^ 8) *
    phi5_d4n (Q ^ 2), ?_, ?_⟩
  · unfold orderE8
    rw [pow_pow_five_sub_one_d4n Q 30, pow_pow_five_sub_one_d4n Q 24,
      pow_pow_five_sub_one_d4n Q 20, pow_pow_five_sub_one_d4n Q 18,
      pow_pow_five_sub_one_d4n Q 14, pow_pow_five_sub_one_d4n Q 12,
      pow_pow_five_sub_one_d4n Q 8, pow_pow_five_sub_one_d4n Q 2]
    ring
  · refine not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_pow_d4n hQ _) ?_) ?_) ?_)
      ?_) ?_) ?_) ?_) ?_ <;>
      exact not_three_dvd_phi5_d4n _

theorem orderE7_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderE7 (Q ^ 5) = orderE7 Q * R ∧ ¬ 3 ∣ R := by
  set R := Q ^ 252 * phi5_d4n (Q ^ 18) * phi5_d4n (Q ^ 14) * phi5_d4n (Q ^ 12) *
    phi5_d4n (Q ^ 10) * phi5_d4n (Q ^ 8) * phi5_d4n (Q ^ 6) * phi5_d4n (Q ^ 2) with hR
  refine ⟨R, ?_, ?_⟩
  · unfold orderE7
    have hN : (Q ^ 5) ^ 63 * ((Q ^ 5) ^ 18 - 1) * ((Q ^ 5) ^ 14 - 1) * ((Q ^ 5) ^ 12 - 1) *
        ((Q ^ 5) ^ 10 - 1) * ((Q ^ 5) ^ 8 - 1) * ((Q ^ 5) ^ 6 - 1) * ((Q ^ 5) ^ 2 - 1) =
        Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 10 - 1) * (Q ^ 8 - 1) *
          (Q ^ 6 - 1) * (Q ^ 2 - 1) * R := by
      rw [pow_pow_five_sub_one_d4n Q 18, pow_pow_five_sub_one_d4n Q 14,
        pow_pow_five_sub_one_d4n Q 12, pow_pow_five_sub_one_d4n Q 10,
        pow_pow_five_sub_one_d4n Q 8, pow_pow_five_sub_one_d4n Q 6,
        pow_pow_five_sub_one_d4n Q 2, hR]
      ring
    have hg : Nat.gcd 2 (Q - 1) ∣ Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) *
        (Q ^ 10 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
      ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one Q)).trans (dvd_mul_left _ _)
    rw [hN, gcd_two_pow_five_sub_one_d4n, Nat.mul_div_right_comm hg]
  · refine not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_pow_d4n hQ _) ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;>
      exact not_three_dvd_phi5_d4n _

theorem orderE6_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderE6 (Q ^ 5) = orderE6 Q * R ∧ ¬ 3 ∣ R := by
  set R := Q ^ 144 * phi5_d4n (Q ^ 12) * phi5_d4n (Q ^ 9) * phi5_d4n (Q ^ 8) *
    phi5_d4n (Q ^ 6) * phi5_d4n (Q ^ 5) * phi5_d4n (Q ^ 2) with hR
  refine ⟨R, ?_, ?_⟩
  · unfold orderE6
    have hN : (Q ^ 5) ^ 36 * ((Q ^ 5) ^ 12 - 1) * ((Q ^ 5) ^ 9 - 1) * ((Q ^ 5) ^ 8 - 1) *
        ((Q ^ 5) ^ 6 - 1) * ((Q ^ 5) ^ 5 - 1) * ((Q ^ 5) ^ 2 - 1) =
        Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 - 1) *
          (Q ^ 2 - 1) * R := by
      rw [pow_pow_five_sub_one_d4n Q 12, pow_pow_five_sub_one_d4n Q 9,
        pow_pow_five_sub_one_d4n Q 8, pow_pow_five_sub_one_d4n Q 6,
        pow_pow_five_sub_one_d4n Q 5, pow_pow_five_sub_one_d4n Q 2, hR]
      ring
    have hg : Nat.gcd 3 (Q - 1) ∣ Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 - 1) * (Q ^ 8 - 1) *
        (Q ^ 6 - 1) * (Q ^ 5 - 1) * (Q ^ 2 - 1) :=
      ((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one Q)).trans (dvd_mul_left _ _)
    rw [hN, gcd_three_pow_five_sub_one_d4n, Nat.mul_div_right_comm hg]
  · refine not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_pow_d4n hQ _) ?_) ?_) ?_) ?_) ?_) ?_ <;>
      exact not_three_dvd_phi5_d4n _

theorem orderTwistedE6_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderTwistedE6 (Q ^ 5) = orderTwistedE6 Q * R ∧ ¬ 3 ∣ R := by
  set R := Q ^ 144 * phi5_d4n (Q ^ 12) * phi10_d4n (Q ^ 9) * phi5_d4n (Q ^ 8) *
    phi5_d4n (Q ^ 6) * phi10_d4n (Q ^ 5) * phi5_d4n (Q ^ 2) with hR
  refine ⟨R, ?_, ?_⟩
  · unfold orderTwistedE6
    have hN : (Q ^ 5) ^ 36 * ((Q ^ 5) ^ 12 - 1) * ((Q ^ 5) ^ 9 + 1) * ((Q ^ 5) ^ 8 - 1) *
        ((Q ^ 5) ^ 6 - 1) * ((Q ^ 5) ^ 5 + 1) * ((Q ^ 5) ^ 2 - 1) =
        Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 + 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 5 + 1) *
          (Q ^ 2 - 1) * R := by
      rw [pow_pow_five_sub_one_d4n Q 12, pow_pow_five_add_one_d4n Q 9,
        pow_pow_five_sub_one_d4n Q 8, pow_pow_five_sub_one_d4n Q 6,
        pow_pow_five_add_one_d4n Q 5, pow_pow_five_sub_one_d4n Q 2, hR]
      ring
    have hg : Nat.gcd 3 (Q + 1) ∣ Q ^ 36 * (Q ^ 12 - 1) * (Q ^ 9 + 1) * (Q ^ 8 - 1) *
        (Q ^ 6 - 1) * (Q ^ 5 + 1) * (Q ^ 2 - 1) := by
      rcases Nat.eq_zero_or_pos Q with rfl | hQ0
      · simp
      · exact ((Nat.gcd_dvd_right _ _).trans (add_one_dvd_sq_sub_one Q hQ0)).trans
          (dvd_mul_left _ _)
    rw [hN, gcd_three_pow_five_add_one_d4n, Nat.mul_div_right_comm hg]
  · refine not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_pow_d4n hQ _) ?_) ?_) ?_) ?_) ?_) ?_
    · exact not_three_dvd_phi5_d4n _
    · exact not_three_dvd_phi10_d4n _
    · exact not_three_dvd_phi5_d4n _
    · exact not_three_dvd_phi5_d4n _
    · exact not_three_dvd_phi10_d4n _
    · exact not_three_dvd_phi5_d4n _

theorem orderTrialityD4_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderTrialityD4 (Q ^ 5) = orderTrialityD4 Q * R ∧ ¬ 3 ∣ R := by
  refine ⟨Q ^ 48 * theta_d4n (Q ^ 4) * phi5_d4n (Q ^ 6) * phi5_d4n (Q ^ 2), ?_, ?_⟩
  · unfold orderTrialityD4
    have h3 : (Q ^ 5) ^ 8 + (Q ^ 5) ^ 4 + 1 = (Q ^ 8 + Q ^ 4 + 1) * theta_d4n (Q ^ 4) := by
      have := trialityFactor_d4n (Q ^ 4)
      rw [show (Q ^ 4) ^ 10 = (Q ^ 5) ^ 8 by ring, show (Q ^ 4) ^ 5 = (Q ^ 5) ^ 4 by ring,
        show (Q ^ 4) ^ 2 = Q ^ 8 by ring] at this
      exact this
    rw [h3, pow_pow_five_sub_one_d4n Q 6, pow_pow_five_sub_one_d4n Q 2]
    ring
  · exact not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_pow_d4n hQ _) (not_three_dvd_theta_d4n _)) (not_three_dvd_phi5_d4n _))
      (not_three_dvd_phi5_d4n _)

theorem orderTwistedF4_pow_five_d4n {Q : ℕ} (hQ : ¬ 3 ∣ Q) :
    ∃ R, orderTwistedF4 (Q ^ 5) = orderTwistedF4 Q * R ∧ ¬ 3 ∣ R := by
  refine ⟨Q ^ 48 * phi10_d4n (Q ^ 6) * phi5_d4n (Q ^ 4) * phi10_d4n (Q ^ 3) * phi5_d4n Q, ?_, ?_⟩
  · unfold orderTwistedF4
    rw [pow_pow_five_add_one_d4n Q 6, pow_pow_five_sub_one_d4n Q 4, pow_pow_five_add_one_d4n Q 3,
      pow_five_sub_one_d4n Q]
    ring
  · exact not_three_dvd_mul_d4n (not_three_dvd_mul_d4n (not_three_dvd_mul_d4n
      (not_three_dvd_mul_d4n (not_three_dvd_pow_d4n hQ _) (not_three_dvd_phi10_d4n _))
      (not_three_dvd_phi5_d4n _)) (not_three_dvd_phi10_d4n _)) (not_three_dvd_phi5_d4n _)

theorem false_of_dvd_of_eq_mul_d4n {M N R : ℕ} (hM : M ≠ 0) (hN : N = M * R) (hR : ¬ 3 ∣ R)
    (h : 174182400 * M ∣ N) : False := by
  rw [hN, mul_comm 174182400 M] at h
  have h1 : 174182400 ∣ R := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hM) h
  exact hR ((show 3 ∣ 174182400 by norm_num).trans h1)

end Subfield

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110n
