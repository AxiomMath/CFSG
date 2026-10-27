module

public import CFSG.Open.OrderForm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Open Finset

@[expose] def fi22Ord : ℕ := 64561751654400

@[expose] def q31 : List ℕ :=
  [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
    3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 5, 25, 7, 11, 13]

theorem fi22Ord_lt : fi22Ord < 2 ^ 46 := by unfold fi22Ord; norm_num

theorem prime_power_dvd_fi22 {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (h : q ^ e ∣ fi22Ord) :
    q ∈ q31 ∧ e ≤ 17 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpF : p ∣ fi22Ord :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h6 : p ∈ ([2, 3, 5, 7, 11, 13] : List ℕ) := by
    have hF : fi22Ord = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 := by unfold fi22Ord; norm_num
    rw [hF] at hpF
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h1 | h1
    · rcases (Nat.Prime.dvd_mul hpp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hpp).1 h2 with h3 | h3
        · rcases (Nat.Prime.dvd_mul hpp).1 h3 with h4 | h4
          · rcases (Nat.Prime.dvd_mul hpp).1 h4 with h5 | h5
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
                (hpp.dvd_of_dvd_pow h5))
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1
                (hpp.dvd_of_dvd_pow h5)))
          · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1
              (hpp.dvd_of_dvd_pow h4))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp
            (by norm_num)).1 h3))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp
          (by norm_num)).1 h2)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp
        (by norm_num)).1 h1)))))
  have hm : p ^ (k * e) ∣ fi22Ord := by rwa [pow_mul]
  have hlt : k * e < 46 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 46 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ fi22Ord := Nat.le_of_dvd (by unfold fi22Ord; norm_num) hm
    have := fi22Ord_lt
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ fi22Ord := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ ([2, 3, 5, 7, 11, 13] : List ℕ), ∀ m < 46, p ^ m ∣ fi22Ord → m ≤ 17 := by
    unfold fi22Ord
    decide +kernel
  have key2 : ∀ p ∈ ([2, 3, 5, 7, 11, 13] : List ℕ), ∀ m < 46, 1 ≤ m → p ^ m ∣ fi22Ord →
      p ^ m ∈ q31 := by
    unfold fi22Ord q31
    decide +kernel
  refine ⟨key2 p h6 k (by omega) hk hkF, ?_⟩
  have := key p h6 (k * e) hlt hm
  have h7 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

theorem coprime_of_dvd_sub_one {q G : ℕ} (hq : 2 ≤ q) (hG : G ∣ q - 1) : Nat.Coprime q G := by
  have h1 : Nat.Coprime (q - 1) ((q - 1) + 1) := by simp
  rw [show (q - 1) + 1 = q by omega] at h1
  exact Nat.Coprime.coprime_dvd_right hG h1.symm

theorem coprime_of_dvd_add_one {q G : ℕ} (hG : G ∣ q + 1) : Nat.Coprime q G := by
  have h1 : Nat.Coprime q (q + 1) := by simp
  exact Nat.Coprime.coprime_dvd_right hG h1

theorem coprime_of_dvd_pow_sub_one {q G n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) (hG : G ∣ q ^ n - 1) :
    Nat.Coprime q G := by
  have h1 : Nat.Coprime (q ^ n - 1) ((q ^ n - 1) + 1) := by simp
  have hpos : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  rw [show (q ^ n - 1) + 1 = q ^ n by omega] at h1
  exact Nat.Coprime.coprime_dvd_right hG
    (Nat.Coprime.coprime_dvd_left (dvd_pow_self q (by omega)) h1.symm)

theorem coprime_of_dvd_pow_add_one {q G n : ℕ} (hn : 1 ≤ n) (hG : G ∣ q ^ n + 1) :
    Nat.Coprime q G := by
  have h1 : Nat.Coprime (q ^ n) (q ^ n + 1) := by simp
  exact Nat.Coprime.coprime_dvd_right hG
    (Nat.Coprime.coprime_dvd_left (dvd_pow_self q (by omega)) h1)

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  exact Nat.sub_one_dvd_pow_sub_one q 2

theorem add_one_dvd_sq_sub_one (q : ℕ) (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  refine ⟨r, ?_⟩
  have : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
  omega

theorem gen_bound {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (hG : Nat.Coprime q G)
    (hmul : G * N = q ^ e * R) (hN : N = fi22Ord) : q ∈ q31 ∧ e ≤ 17 := by
  have h1 : q ^ e ∣ G * fi22Ord := ⟨R, by rw [← hN, hmul]⟩
  exact prime_power_dvd_fi22 hq he ((Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1)

theorem orderA_ne {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) : orderA n q ≠ fi22Ord := by
  intro h
  have hq2 := hq.two_le
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hGd : Nat.gcd (n + 1) (q - 1) ∣ q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans (sub_one_dvd_sq_sub_one q)).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q - 1) * orderA n q =
      q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 2 (n + 1), (q ^ i - 1) := Nat.mul_div_cancel' hGd
  have he1 : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
  obtain ⟨hq31, he⟩ := gen_bound hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 21 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4, 5] : List ℕ), ∀ q ∈ q31, orderA n q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid n (by simp; omega) q hq31 h

theorem orderTwistedA_ne {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) :
    orderTwistedA n q ≠ fi22Ord := by
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
  obtain ⟨hq31, he⟩ := gen_bound hq he1 (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul h
  have hn5 : n ≤ 5 := by
    by_contra hc
    push Not at hc
    have : 21 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    omega
  have grid : ∀ n ∈ ([1, 2, 3, 4, 5] : List ℕ), ∀ q ∈ q31, orderTwistedA n q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid n (by simp; omega) q hq31 h

theorem orderBC_ne {n q : ℕ} (hn : 1 ≤ n) (hq : IsPrimePow q) : orderBC n q ≠ fi22Ord := by
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
  obtain ⟨hq31, he⟩ := gen_bound hq he1 (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _))
    hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    nlinarith
  have grid : ∀ n ∈ ([1, 2, 3, 4] : List ℕ), ∀ q ∈ q31, orderBC n q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid n (by simp; omega) q hq31 h

theorem orderD_ne {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) : orderD n q ≠ fi22Ord := by
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
  obtain ⟨hq31, he⟩ := gen_bound hq he1
    (coprime_of_dvd_pow_sub_one hq2 (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ q31, orderD 4 q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact grid q hq31 h

theorem orderTwistedD_ne {n q : ℕ} (hn : 4 ≤ n) (hq : IsPrimePow q) :
    orderTwistedD n q ≠ fi22Ord := by
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
  obtain ⟨hq31, he⟩ := gen_bound hq he1
    (coprime_of_dvd_pow_add_one (by omega) (Nat.gcd_dvd_right _ _)) hmul h
  have hn4 : n ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul hc (by omega)
    omega
  have grid : ∀ q ∈ q31, orderTwistedD 4 q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  have : n = 4 := by omega
  subst this
  exact grid q hq31 h

theorem orderE6_ne {q : ℕ} (hq : IsPrimePow q) : orderE6 q ≠ fi22Ord := by
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

theorem orderTwistedE6_ne {q : ℕ} (hq : IsPrimePow q) : orderTwistedE6 q ≠ fi22Ord := by
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

theorem orderE7_ne {q : ℕ} (hq : IsPrimePow q) : orderE7 q ≠ fi22Ord := by
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
    (hN : N = fi22Ord) : q ∈ q31 ∧ e ≤ 17 :=
  gen_bound hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

theorem orderE8_ne {q : ℕ} (hq : IsPrimePow q) : orderE8 q ≠ fi22Ord := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) *
    (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderE8; ring) h
  omega

theorem orderF4_ne {q : ℕ} (hq : IsPrimePow q) : orderF4 q ≠ fi22Ord := by
  intro h
  obtain ⟨-, he⟩ := gen_bound' (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) h
  omega

theorem orderG2_ne {q : ℕ} (hq : IsPrimePow q) : orderG2 q ≠ fi22Ord := by
  intro h
  obtain ⟨hq31, -⟩ := gen_bound' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq (by norm_num)
    (by unfold orderG2; ring) h
  have grid : ∀ q ∈ q31, orderG2 q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid q hq31 h

theorem orderTrialityD4_ne {q : ℕ} (hq : IsPrimePow q) : orderTrialityD4 q ≠ fi22Ord := by
  intro h
  obtain ⟨hq31, -⟩ := gen_bound' (e := 12) (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1))
    hq (by norm_num) (by unfold orderTrialityD4; ring) h
  have grid : ∀ q ∈ q31, orderTrialityD4 q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid q hq31 h

theorem orderSuzuki_ne {q : ℕ} (hq : IsPrimePow q) : orderSuzuki q ≠ fi22Ord := by
  intro h
  obtain ⟨hq31, -⟩ := gen_bound' (e := 2) (R := (q ^ 2 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderSuzuki; ring) h
  have grid : ∀ q ∈ q31, orderSuzuki q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid q hq31 h

theorem orderRee_ne {q : ℕ} (hq : IsPrimePow q) : orderRee q ≠ fi22Ord := by
  intro h
  obtain ⟨hq31, -⟩ := gen_bound' (e := 3) (R := (q ^ 3 + 1) * (q - 1)) hq (by norm_num)
    (by unfold orderRee; ring) h
  have grid : ∀ q ∈ q31, orderRee q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid q hq31 h

theorem orderTwistedF4_ne {q : ℕ} (hq : IsPrimePow q) : orderTwistedF4 q ≠ fi22Ord := by
  intro h
  obtain ⟨hq31, -⟩ := gen_bound' (e := 12) (R := (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1))
    hq (by norm_num) (by unfold orderTwistedF4; ring) h
  have grid : ∀ q ∈ q31, orderTwistedF4 q ≠ fi22Ord := by
    unfold fi22Ord q31
    decide +kernel
  exact grid q hq31 h

theorem orderTits_ne : orderTits ≠ fi22Ord := by
  unfold orderTits fi22Ord
  norm_num

@[expose] def lieOrderFormula : TauCeti.LieTypeIndex → ℕ
  | .A n q => orderA n q.card
  | .twistedA n q => orderTwistedA n q.card
  | .B n q => orderBC n q.card
  | .C n q => orderBC n q.card
  | .D n q => orderD n q.card
  | .twistedD n q => orderTwistedD n q.card
  | .E6 q => orderE6 q.card
  | .E7 q => orderE7 q.card
  | .E8 q => orderE8 q.card
  | .F4 q => orderF4 q.card
  | .G2 q => orderG2 q.card
  | .twistedE6 q => orderTwistedE6 q.card
  | .trialityD4 q => orderTrialityD4 q.card
  | .suzuki m => orderSuzuki (2 ^ (2 * m + 1))
  | .reeG2 m => orderRee (3 ^ (2 * m + 1))
  | .reeF4 m => orderTwistedF4 (2 ^ (2 * m + 1))
  | .tits => orderTits

theorem lieOrderFormula_ne_fi22Ord {d : TauCeti.LieTypeIndex} (hd : d.Valid) :
    lieOrderFormula d ≠ fi22Ord := by
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

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
