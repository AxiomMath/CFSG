module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.HSLie

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula coprime_of_dvd_sub_one
  coprime_of_dvd_add_one coprime_of_dvd_pow_sub_one coprime_of_dvd_pow_add_one
  sub_one_dvd_sq_sub_one add_one_dvd_sq_sub_one)

open CFSG.Open Finset

@[expose] def hsOrd : ℕ := 44352000

theorem hsOrd_eq : hsOrd = 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 := by unfold hsOrd; norm_num

@[expose] def q16 : List ℕ := [2, 4, 8, 16, 32, 64, 128, 256, 512, 3, 9, 5, 25, 125, 7, 11]

theorem hsOrd_lt : hsOrd < 2 ^ 26 := by unfold hsOrd; norm_num

theorem prime_power_dvd_hs {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (h : q ^ e ∣ hsOrd) :
    q ∈ q16 ∧ e ≤ 9 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ hsOrd :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h5 : p ∈ ([2, 3, 5, 7, 11] : List ℕ) := by
    rw [hsOrd_eq] at hpF
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h1 | h1
    · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hpp).1 h2 with h3 | h3
        · rcases (Nat.Prime.dvd_mul hpp).1 h3 with h4 | h4
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
              (hpp.dvd_of_dvd_pow h4))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1
              (hpp.dvd_of_dvd_pow h4)))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1
            (hpp.dvd_of_dvd_pow h3))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp
          (by norm_num)).1 h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp
        (by norm_num)).1 h1))))
  have hm : p ^ (k * e) ∣ hsOrd := by rwa [pow_mul]
  have hlt : k * e < 26 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 26 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ hsOrd := Nat.le_of_dvd (by unfold hsOrd; norm_num) hm
    have := hsOrd_lt
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ hsOrd := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ ([2, 3, 5, 7, 11] : List ℕ), ∀ m < 26, p ^ m ∣ hsOrd → m ≤ 9 := by
    unfold hsOrd
    decide +kernel
  have key2 : ∀ p ∈ ([2, 3, 5, 7, 11] : List ℕ), ∀ m < 26, 1 ≤ m → p ^ m ∣ hsOrd →
      p ^ m ∈ q16 := by
    unfold hsOrd q16
    decide +kernel
  refine ⟨key2 p h5 k (by omega) hk hkF, ?_⟩
  have := key p h5 (k * e) hlt hm
  have h8 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

theorem gen_bound {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (hG : Nat.Coprime q G)
    (hmul : G * N = q ^ e * R) (hN : N = hsOrd) : q ∈ q16 ∧ e ≤ 9 := by
  have h1 : q ^ e ∣ G * hsOrd := ⟨R, by rw [← hN, hmul]⟩
  exact prime_power_dvd_hs hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

theorem orderA_ne {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) : orderA n q ≠ hsOrd := by
  intro h
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq16, he⟩ := gen_bound hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 21 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4, 5] : List ℕ), ∀ q ∈ q16, orderA n q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid n (by simp; omega) q hq16 h

theorem orderTwistedA_ne {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) :
    orderTwistedA n q ≠ hsOrd := by
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
  obtain ⟨hq16, he⟩ := gen_bound hq he1 (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 21 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4, 5] : List ℕ), ∀ q ∈ q16, orderTwistedA n q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid n (by simp; omega) q hq16 h

theorem orderBC_ne {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) : orderBC n q ≠ hsOrd := by
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
  obtain ⟨hq16, he⟩ := gen_bound hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    nlinarith
  have grid : ∀ n ∈ ([1, 2, 3, 4] : List ℕ), ∀ q ∈ q16, orderBC n q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid n (by simp; omega) q hq16 h

theorem orderD_ne {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) : orderD n q ≠ hsOrd := by
  intro h
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
  obtain ⟨hq16, he⟩ := gen_bound hq he1
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ q16, orderD 4 q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact grid q hq16 h

theorem orderTwistedD_ne {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    orderTwistedD n q ≠ hsOrd := by
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
  obtain ⟨hq16, he⟩ := gen_bound hq he1
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ q16, orderTwistedD 4 q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact grid q hq16 h

theorem orderE6_ne {q : ℕ} (hq : IsPrimePow q) : orderE6 q ≠ hsOrd := by
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
  obtain ⟨-, he⟩ := gen_bound hq (by norm_num) (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  omega

theorem orderTwistedE6_ne {q : ℕ} (hq : IsPrimePow q) : orderTwistedE6 q ≠ hsOrd := by
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
  obtain ⟨-, he⟩ := gen_bound hq (by norm_num) (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _))
    hmul h
  omega

theorem orderE7_ne {q : ℕ} (hq : IsPrimePow q) : orderE7 q ≠ hsOrd := by
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
  obtain ⟨-, he⟩ := gen_bound hq (by norm_num) (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  omega

theorem gen_bound' {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (hmul : N = q ^ e * R)
    (hN : N = hsOrd) : q ∈ q16 ∧ e ≤ 9 :=
  gen_bound hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

theorem orderE8_ne {q : ℕ} (hq : IsPrimePow q) : orderE8 q ≠ hsOrd := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) *
    (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

theorem orderF4_ne {q : ℕ} (hq : IsPrimePow q) : orderF4 q ≠ hsOrd := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) h
  omega

theorem orderG2_ne {q : ℕ} (hq : IsPrimePow q) : orderG2 q ≠ hsOrd := by
  intro h
  obtain ⟨hq16, -⟩ := gen_bound' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderG2; ring) h
  have grid : ∀ q ∈ q16, orderG2 q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid q hq16 h

theorem orderTrialityD4_ne {q : ℕ} (hq : IsPrimePow q) : orderTrialityD4 q ≠ hsOrd := by
  intro h
  obtain ⟨hq16, -⟩ := gen_bound' (e := 12) (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
    hq (by norm_num) (by unfold orderTrialityD4; ring) h
  have grid : ∀ q ∈ q16, orderTrialityD4 q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid q hq16 h

theorem orderSuzuki_ne {q : ℕ} (hq : IsPrimePow q) : orderSuzuki q ≠ hsOrd := by
  intro h
  obtain ⟨hq16, -⟩ := gen_bound' (e := 2) (R := (q ^ 2 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderSuzuki; ring) h
  have grid : ∀ q ∈ q16, orderSuzuki q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid q hq16 h

theorem orderRee_ne {q : ℕ} (hq : IsPrimePow q) : orderRee q ≠ hsOrd := by
  intro h
  obtain ⟨hq16, -⟩ := gen_bound' (e := 3) (R := (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderRee; ring) h
  have grid : ∀ q ∈ q16, orderRee q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid q hq16 h

theorem orderTwistedF4_ne {q : ℕ} (hq : IsPrimePow q) : orderTwistedF4 q ≠ hsOrd := by
  intro h
  obtain ⟨hq16, -⟩ := gen_bound' (e := 12) (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderTwistedF4; ring) h
  have grid : ∀ q ∈ q16, orderTwistedF4 q ≠ hsOrd := by
    unfold hsOrd q16
    decide +kernel
  exact grid q hq16 h

theorem orderTits_ne : orderTits ≠ hsOrd := by
  unfold orderTits hsOrd
  norm_num

theorem lieOrderFormula_ne_hsOrd {d : TauCeti.LieTypeIndex} (hd : d.Valid) :
    lieOrderFormula d ≠ hsOrd := by
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hd).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases d with
  | A n q => exact orderA_ne hs.1 q.isPrimePow_card
  | twistedA n q => exact orderTwistedA_ne (by omega : 1 ≤ n) q.isPrimePow_card
  | B n q => exact orderBC_ne (by omega : 1 ≤ n) q.isPrimePow_card
  | C n q => exact orderBC_ne (by omega : 1 ≤ n) q.isPrimePow_card
  | D n q => exact orderD_ne hs q.isPrimePow_card
  | twistedD n q => exact orderTwistedD_ne hs q.isPrimePow_card
  | E6 q => exact orderE6_ne q.isPrimePow_card
  | E7 q => exact orderE7_ne q.isPrimePow_card
  | E8 q => exact orderE8_ne q.isPrimePow_card
  | F4 q => exact orderF4_ne q.isPrimePow_card
  | G2 q => exact orderG2_ne q.isPrimePow_card
  | twistedE6 q => exact orderTwistedE6_ne q.isPrimePow_card
  | trialityD4 q => exact orderTrialityD4_ne q.isPrimePow_card
  | suzuki m => exact orderSuzuki_ne (Nat.prime_two.isPrimePow.pow (by omega))
  | reeG2 m => exact orderRee_ne (Nat.prime_three.isPrimePow.pow (by omega))
  | reeF4 m => exact orderTwistedF4_ne (Nat.prime_two.isPrimePow.pow (by omega))
  | tits => exact orderTits_ne

end CFSG.HardMathSupport.Dickson.BMRows.HSLie
