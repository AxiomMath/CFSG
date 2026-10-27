module

public import CFSG.LocalAnalysis.SeitzReduction.CrossCharEven
public import CFSG.HardMathSupport.Solomon.Proving.L2OrderUnique
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharOdd

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923


theorem key_of_lt_pow {q C E N : ℕ} (hq : 2 ≤ q) (hC : C < q ^ E) (hx : 9 ≤ q ^ N)
    (hE : E + 1 ≤ 2 * N) (h3 : 3 ≤ q ∨ E + 2 ≤ 2 * N) :
    2 * C < (q ^ N - 1) * (q ^ N - 2) := by
  have hsq : (q ^ N) ^ 2 = q ^ (2 * N) := by rw [← pow_mul]; ring_nf
  generalize q ^ N = x at hx hsq
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 9 := ⟨x - 9, by omega⟩
  simp only [show y + 9 - 1 = y + 8 by omega, show y + 9 - 2 = y + 7 by omega]
  rcases h3 with h3 | h3
  · have h1 : 3 * C < (y + 9) ^ 2 := by
      calc 3 * C < q * q ^ E := by nlinarith
        _ = q ^ (E + 1) := by ring
        _ ≤ q ^ (2 * N) := Nat.pow_le_pow_right (by omega) hE
        _ = (y + 9) ^ 2 := hsq.symm
    nlinarith
  · have h1 : 4 * C < (y + 9) ^ 2 := by
      calc 4 * C < 4 * q ^ E := by omega
        _ ≤ q ^ 2 * q ^ E := Nat.mul_le_mul_right _ (by nlinarith)
        _ = q ^ (E + 2) := by rw [← pow_add]; ring_nf
        _ ≤ q ^ (2 * N) := Nat.pow_le_pow_right (by omega) h3
        _ = (y + 9) ^ 2 := hsq.symm
    nlinarith

theorem cop_of_lin {a b : ℕ} (u v : ℤ) (h : u * a + v * b = 1) : Nat.Coprime a b :=
  Nat.isCoprime_iff_coprime.1 ⟨u, v, h⟩

theorem isPrimePow_or_one {p k : ℕ} (hp : p.Prime) : p ^ k = 1 ∨ IsPrimePow (p ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · left; simp
  · right; exact hp.isPrimePow.pow hk.ne'

theorem dvd_or_dvd_of_coprime {x a b : ℕ} (hx : x = 1 ∨ IsPrimePow x) (hab : Nat.Coprime a b)
    (h : x ∣ a * b) : x ∣ a ∨ x ∣ b := by
  rcases hx with rfl | hx
  · exact Or.inl (one_dvd _)
  · exact (hab.isPrimePow_dvd_mul hx).1 h

theorem le_succ_of_dvd_l2 {x r M : ℕ} (hx : x = 1 ∨ IsPrimePow x) (hr : 3 ≤ r) (hdvd : x ∣ M)
    (hodd : Odd r → 2 * M + r = r ^ 3) (heven : Even r → M + r = r ^ 3) : x ≤ r + 1 := by
  rcases Nat.even_or_odd r with hev | hod
  · have hM := heven hev
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hM' : M = (s + 1) * (s * (s + 2)) := by
      have : M + (s + 1) = (s + 1) ^ 3 := hM
      nlinarith
    rw [hM'] at hdvd
    have hso : Odd s := by
      obtain ⟨u, hu⟩ := hev
      exact ⟨u - 1, by omega⟩
    have hc1 : Nat.Coprime (s + 1) (s * (s + 2)) := by
      rw [Nat.coprime_mul_iff_right]
      constructor
      · rw [Nat.coprime_comm]
        exact (Nat.coprime_self_add_right (m := s) (n := 1)).2 (Nat.coprime_one_right s)
      · rw [show s + 2 = (s + 1) + 1 by ring]
        exact (Nat.coprime_self_add_right (m := s + 1) (n := 1)).2 (Nat.coprime_one_right (s + 1))
    rcases dvd_or_dvd_of_coprime hx hc1 hdvd with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have hc2 : Nat.Coprime s (s + 2) := by
        rw [Nat.coprime_self_add_right]
        exact Nat.coprime_two_right.2 hso
      rcases dvd_or_dvd_of_coprime hx hc2 h with h' | h'
      · have := Nat.le_of_dvd (by omega) h'; omega
      · have := Nat.le_of_dvd (by omega) h'; omega
  · have h2M := hodd hod
    obtain ⟨m, rfl⟩ := hod
    have hM' : M = 2 * (m * (m + 1) * (2 * m + 1)) := by
      have : 2 * M + (2 * m + 1) = (2 * m + 1) ^ 3 := h2M
      nlinarith
    rw [hM'] at hdvd
    have hm1 : 1 ≤ m := by omega
    have hmm : Nat.Coprime m (m + 1) := cop_of_lin (-1) 1 (by push_cast; ring)
    have hcm : Nat.Coprime (m * (m + 1)) (2 * m + 1) :=
      Nat.coprime_mul_iff_left.2 ⟨cop_of_lin (-2) 1 (by push_cast; ring),
        cop_of_lin 2 (-1) (by push_cast; ring)⟩
    rcases hx with rfl | hpp
    · omega
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ'] at hdvd ⊢
      have h1 : 2 ^ k' ∣ m * (m + 1) * (2 * m + 1) :=
        Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
      have hco : Nat.Coprime (2 ^ k') (2 * m + 1) :=
        Nat.Coprime.pow_left k' (Nat.coprime_two_left.2 ⟨m, rfl⟩)
      have h2 : 2 ^ k' ∣ m * (m + 1) := hco.dvd_of_dvd_mul_right h1
      rcases dvd_or_dvd_of_coprime (isPrimePow_or_one Nat.prime_two) hmm h2 with h3 | h3
      · have := Nat.le_of_dvd (by omega) h3; omega
      · have := Nat.le_of_dvd (by omega) h3; omega
    · have hco : Nat.Coprime (p ^ k) 2 :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      have h1 : p ^ k ∣ m * (m + 1) * (2 * m + 1) := hco.dvd_of_dvd_mul_left hdvd
      rcases dvd_or_dvd_of_coprime (Or.inr hpp) hcm h1 with h2 | h2
      · rcases dvd_or_dvd_of_coprime (Or.inr hpp) hmm h2 with h3 | h3
        · have := Nat.le_of_dvd (by omega) h3; omega
        · have := Nat.le_of_dvd (by omega) h3; omega
      · have := Nat.le_of_dvd (by omega) h2; omega


theorem nine_le_pow {q N : ℕ} (hq : 2 ≤ q) (h : (3 ≤ q ∧ 2 ≤ N) ∨ 4 ≤ N) : 9 ≤ q ^ N := by
  rcases h with ⟨h3, h2⟩ | h4
  · calc 9 = 3 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ q ^ N := Nat.pow_le_pow_right (by omega) h2
  · calc 9 ≤ 2 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
      _ ≤ q ^ N := Nat.pow_le_pow_right (by omega) h4

theorem key_exc {q C S N : ℕ} (hq : 2 ≤ q) (hC : C ≤ q ^ S) (hS : S + 3 ≤ 2 * N) (hN : 4 ≤ N) :
    2 * C < (q ^ N - 1) * (q ^ N - 2) :=
  key_of_lt_pow hq (hC.trans_lt (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self S)))
    (nine_le_pow hq (Or.inr hN)) (by omega) (Or.inr (by omega))

open Finset CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.CrossChar in
theorem cofactor_key {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (ht : t ≠ .Tits) (hA : ¬ (t = .PSL ∧ n = 2)) (hX : ¬ (t = .PSL ∧ n = 3 ∧ p ^ f = 2)) :
    2 * lieOrderCofactor t n (p ^ f) <
      ((p ^ f) ^ lieSylowExponent t n - 1) * ((p ^ f) ^ lieSylowExponent t n - 2) := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hq1 : 1 ≤ p ^ f := by omega
  generalize hqdef : p ^ f = q at hadm hq2 hq1 hX ⊢
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    have hn3 : 3 ≤ n := by
      by_contra h
      exact hA ⟨rfl, by omega⟩
    have hC := prod_Icc_two_sub_one_lt hq1 hn
    have h2N := two_mul_tri n
    show 2 * (∏ i ∈ Icc 2 n, (q ^ i - 1)) < (q ^ (n * (n - 1) / 2) - 1) * (q ^ (n * (n - 1) / 2) - 2)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp only [show k + 3 - 1 = k + 2 by omega] at h2N hC ⊢
    generalize hNdef : (k + 3) * (k + 2) / 2 = N at h2N hC ⊢
    have hNk : k + 3 ≤ N := by nlinarith
    refine key_of_lt_pow hq2 hC ?_ ?_ ?_
    · by_cases hq3 : 3 ≤ q
      · exact nine_le_pow hq2 (Or.inl ⟨hq3, by omega⟩)
      · have hq' : q = 2 := by omega
        subst hq'
        have hk : 1 ≤ k := by
          by_contra h
          exact hX ⟨rfl, by omega, rfl⟩
        exact nine_le_pow hq2 (Or.inr (by nlinarith))
    · omega
    · by_cases hq3 : 3 ≤ q
      · exact Or.inl hq3
      · right
        have hq' : q = 2 := by omega
        subst hq'
        have hk : 1 ≤ k := by
          by_contra h
          exact hX ⟨rfl, by omega, rfl⟩
        have : k + 4 ≤ N := by nlinarith
        omega
  case PSU =>
    obtain ⟨-, -, hn, hn3q⟩ := hadm
    have hC := prod_psu_lt hq2 (by omega : 2 ≤ n)
    have h2N := two_mul_tri n
    show 2 * (∏ i ∈ Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1)) <
      (q ^ (n * (n - 1) / 2) - 1) * (q ^ (n * (n - 1) / 2) - 2)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp only [show k + 3 - 1 = k + 2 by omega] at h2N hC ⊢
    generalize hNdef : (k + 3) * (k + 2) / 2 = N at h2N hC ⊢
    have hNk : k + 3 ≤ N := by nlinarith
    refine key_of_lt_pow hq2 hC ?_ ?_ ?_
    · by_cases hq3 : 3 ≤ q
      · exact nine_le_pow hq2 (Or.inl ⟨hq3, by omega⟩)
      · have hq' : q = 2 := by omega
        subst hq'
        have hk : 1 ≤ k := by
          by_contra h
          exact hn3q (by rw [show k = 0 by omega, hqdef])
        exact nine_le_pow hq2 (Or.inr (by nlinarith))
    · omega
    · by_cases hq3 : 3 ≤ q
      · exact Or.inl hq3
      · right
        have hq' : q = 2 := by omega
        subst hq'
        have hk : 1 ≤ k := by
          by_contra h
          exact hn3q (by rw [show k = 0 by omega, hqdef])
        have : k + 4 ≤ N := by nlinarith
        omega
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hC := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n)
    show 2 * (∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1)) < (q ^ (n ^ 2) - 1) * (q ^ (n ^ 2) - 2)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    refine key_of_lt_pow hq2 hC (nine_le_pow hq2 (Or.inr (by nlinarith))) (by nlinarith)
      (Or.inr (by nlinarith))
  case POmegaOdd =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hC := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n)
    show 2 * (∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1)) < (q ^ (n ^ 2) - 1) * (q ^ (n ^ 2) - 2)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    refine key_of_lt_pow hq2 hC (nine_le_pow hq2 (Or.inr (by nlinarith))) (by nlinarith)
      (Or.inr (by nlinarith))
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    have hC : (q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) <
        q ^ (n + (n - 1) * (n - 1 + 1)) := by
      rw [pow_add]
      exact Nat.mul_lt_mul'' (pow_sub_one_lt_pow hq1 n) hP
    show 2 * ((q ^ n - 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) <
      (q ^ (n * (n - 1)) - 1) * (q ^ (n * (n - 1)) - 2)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show k + 4 - 1 = k + 3 by omega] at hC ⊢
    refine key_of_lt_pow hq2 hC (nine_le_pow hq2 (Or.inr (by nlinarith))) (by nlinarith)
      (Or.inr (by nlinarith))
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hP := prod_Icc_one_sub_one_lt hq1 (by omega : 1 ≤ n - 1)
    have hX' : q ^ n + 1 ≤ q ^ (n + 1) := by
      rw [pow_succ]
      have := Nat.one_le_pow n q hq1
      nlinarith
    have hC : (q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1) <
        q ^ (n + 1 + (n - 1) * (n - 1 + 1)) := by
      rw [pow_add]
      exact Nat.mul_lt_mul_of_le_of_lt hX' hP (by positivity)
    show 2 * ((q ^ n + 1) * ∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) <
      (q ^ (n * (n - 1)) - 1) * (q ^ (n * (n - 1)) - 2)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show k + 4 - 1 = k + 3 by omega] at hC ⊢
    refine key_of_lt_pow hq2 hC (nine_le_pow hq2 (Or.inr (by nlinarith))) (by nlinarith)
      (Or.inr (by nlinarith))
  case G2 =>
    have hC : lieOrderCofactor .G2 n q ≤ q ^ 8 := by
      show (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 8
      calc (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 8 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case F4 =>
    have hC : lieOrderCofactor .F4 n q ≤ q ^ 28 := by
      show (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 28
      calc (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 28 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case E6 =>
    have hC : lieOrderCofactor .E6 n q ≤ q ^ 42 := by
      show (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) ≤
        q ^ 42
      calc (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 9 * q ^ 8 * q ^ 6 * q ^ 5 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 42 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case E7 =>
    have hC : lieOrderCofactor .E7 n q ≤ q ^ 70 := by
      show (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 70
      calc (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
            (q ^ 6 - 1) * (q ^ 2 - 1)
          ≤ q ^ 18 * q ^ 14 * q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 70 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case E8 =>
    have hC : lieOrderCofactor .E8 n q ≤ q ^ 128 := by
      show (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
        (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1) ≤ q ^ 128
      calc (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
            (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
          ≤ q ^ 30 * q ^ 24 * q ^ 20 * q ^ 18 * q ^ 14 * q ^ 12 * q ^ 8 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 128 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case twistedE6 =>
    have hC : lieOrderCofactor .twistedE6 n q ≤ q ^ 44 := by
      show (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) ≤
        q ^ 44
      calc (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
          ≤ q ^ 12 * q ^ 10 * q ^ 8 * q ^ 6 * q ^ 6 * q ^ 2 := by
            gcongr
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq2 9
            · exact Nat.sub_le _ _
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq2 5
            · exact Nat.sub_le _ _
        _ = q ^ 44 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case trialityD4 =>
    have hC : lieOrderCofactor .trialityD4 n q ≤ q ^ 17 := by
      show (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 17
      have h8 : q ^ 8 + q ^ 4 + 1 ≤ q ^ 9 := by
        have h4 : q ^ 4 + 1 ≤ q ^ 8 := by
          have : q ^ 4 + 1 ≤ q ^ 5 := pow_add_one_le_pow_succ hq2 4
          exact this.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
        have : q ^ 8 + 1 ≤ q ^ 9 := pow_add_one_le_pow_succ hq2 8
        nlinarith [Nat.one_le_pow 8 q (by omega)]
      calc (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 9 * q ^ 6 * q ^ 2 := by
            gcongr <;> exact Nat.sub_le _ _
        _ = q ^ 17 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case twistedB2 =>
    obtain ⟨-, -, -, hp2, -, hf3⟩ := hadm
    have hq8 : 8 ≤ q := by
      rw [← hqdef, hp2]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    have hC : lieOrderCofactor .twistedB2 n q < q ^ 3 := by
      show (q ^ 2 + 1) * (q - 1) < q ^ 3
      have h1 : q - 1 + 1 = q := by omega
      have h2 : (q ^ 2 + 1) * (q - 1) + q ^ 2 = q ^ 3 + (q - 1) := by
        rw [← h1]; simp only [Nat.add_sub_cancel]; ring
      have h3 : q - 1 < q ^ 2 := by nlinarith
      omega
    exact key_of_lt_pow hq2 hC
      (by show 9 ≤ q ^ lieSylowExponent .twistedB2 n; exact nine_le_pow hq2 (Or.inl ⟨by omega, by simp [lieSylowExponent]⟩))
      (by simp [lieSylowExponent]) (Or.inl (by omega))
  case twistedG2 =>
    obtain ⟨-, -, -, hp3, -, hf3⟩ := hadm
    have hq27 : 27 ≤ q := by
      rw [← hqdef, hp3]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    have hC : lieOrderCofactor .twistedG2 n q < q ^ 4 := by
      show (q ^ 3 + 1) * (q - 1) < q ^ 4
      obtain ⟨u, rfl⟩ : ∃ u, q = u + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hu : u < (u + 1) ^ 3 :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self u) (Nat.le_self_pow (by norm_num) _)
      calc ((u + 1) ^ 3 + 1) * u = (u + 1) ^ 3 * u + u := by ring
        _ < (u + 1) ^ 3 * u + (u + 1) ^ 3 := by omega
        _ = (u + 1) ^ 4 := by ring
    exact key_of_lt_pow hq2 hC
      (by show 9 ≤ q ^ lieSylowExponent .twistedG2 n; exact nine_le_pow hq2 (Or.inl ⟨by omega, by simp [lieSylowExponent]⟩))
      (by simp [lieSylowExponent]) (Or.inl (by omega))
  case twistedF4 =>
    have hC : lieOrderCofactor .twistedF4 n q ≤ q ^ 16 := by
      show (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 16
      calc (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) ≤ q ^ 7 * q ^ 4 * q ^ 4 * q := by
            gcongr
            · exact pow_add_one_le_pow_succ hq2 6
            · exact Nat.sub_le _ _
            · exact pow_add_one_le_pow_succ hq2 3
            · exact Nat.sub_le _ _
        _ = q ^ 16 := by ring
    exact key_exc hq2 hC (by simp [lieSylowExponent]) (by simp [lieSylowExponent])
  case Tits => exact absurd rfl ht


open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof in
theorem lie_order_ne_l2 {t : StatedLieTag} {n p f M r : ℕ} (hadm : StatedLieAdmissible t n p f)
    (ht : t ≠ .Tits) (hA : ¬ (t = .PSL ∧ n = 2))
    (hM : M * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) (hr : 10 ≤ r)
    (hodd : Odd r → 2 * M + r = r ^ 3) (heven : Even r → M + r = r ^ 3) : False := by
  have hp : p.Prime := hadm.1
  have hnum := lieOrderNumerator_eq hadm
  have hD1 : 1 ≤ lieOrderDivisor t n (p ^ f) :=
    Nat.one_le_iff_ne_zero.2 (lieOrderDivisor_ne_zero hadm)
  have hMle : M ≤ (p ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (p ^ f) := by
    rw [← hnum, ← hM]
    exact Nat.le_mul_of_pos_right M hD1
  have hxM : (p ^ f) ^ lieSylowExponent t n ∣ M := by
    have hco : Nat.Coprime ((p ^ f) ^ lieSylowExponent t n) (lieOrderDivisor t n (p ^ f)) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _
        ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_lieOrderDivisor hadm)))
    refine hco.dvd_of_dvd_mul_right ?_
    rw [hM, hnum]
    exact dvd_mul_right _ _
  have hxpp : (p ^ f) ^ lieSylowExponent t n = 1 ∨ IsPrimePow ((p ^ f) ^ lieSylowExponent t n) := by
    rw [← pow_mul]; exact isPrimePow_or_one hp
  have hxr := le_succ_of_dvd_l2 hxpp (by omega) hxM hodd heven
  have h100 : 100 ≤ r * r := by nlinarith
  have hr3 : 100 * r ≤ r ^ 3 := by nlinarith
  by_cases hX : t = .PSL ∧ n = 3 ∧ p ^ f = 2
  · obtain ⟨rfl, rfl, hq⟩ := hX
    have hMle' : M ≤ 168 := by
      refine hMle.trans ?_
      rw [hq]
      decide
    rcases Nat.even_or_odd r with hev | hod
    · have := heven hev
      omega
    · have := hodd hod
      omega
  · have hkey := cofactor_key hadm ht hA hX
    generalize (p ^ f) ^ lieSylowExponent t n = x at hkey hxr hMle
    generalize lieOrderCofactor t n (p ^ f) = C at hkey hMle
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 3 := by
      rcases Nat.lt_or_ge x 3 with h | h
      · exfalso
        interval_cases x <;> simp at hkey
      · exact ⟨x - 3, by omega⟩
    simp only [show y + 3 - 1 = y + 2 by omega, show y + 3 - 2 = y + 1 by omega] at hkey
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hs : y + 1 ≤ s := by omega
    have h3 : (y + 3) * ((y + 2) * (y + 1)) ≤ (s + 2) * ((s + 1) * s) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    have h2M : (y + 3) * ((y + 2) * (y + 1)) ≤ 2 * M := by
      rcases Nat.even_or_odd (s + 1) with hev | hod
      · have h1 := heven hev
        have : M = (s + 2) * ((s + 1) * s) := by nlinarith
        omega
      · have h1 := hodd hod
        have : 2 * M = (s + 2) * ((s + 1) * s) := by nlinarith
        omega
    have h5 : (y + 3) * ((y + 2) * (y + 1)) ≤ (y + 3) * (2 * C) := by
      calc (y + 3) * ((y + 2) * (y + 1)) ≤ 2 * M := h2M
        _ ≤ 2 * ((y + 3) * C) := by omega
        _ = (y + 3) * (2 * C) := by ring
    have h4 := Nat.le_of_mul_le_mul_left h5 (by omega)
    omega


open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof in
theorem sylow_dvd_of_order {t : StatedLieTag} {n p f M : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hM : M * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) :
    (p ^ f) ^ lieSylowExponent t n ∣ M := by
  have hp : p.Prime := hadm.1
  have hnum := lieOrderNumerator_eq hadm
  have hco : Nat.Coprime ((p ^ f) ^ lieSylowExponent t n) (lieOrderDivisor t n (p ^ f)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_lieOrderDivisor hadm)))
  refine hco.dvd_of_dvd_mul_right ?_
  rw [hM, hnum]
  exact dvd_mul_right _ _

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof in
theorem exists_noncomm_of_simple_of_order {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hM : Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f))
    (hN : 2 ≤ f * lieSylowExponent t n) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  letI : CommGroup X := { ‹Group X› with mul_comm := fun a b => hcon a b }
  have hprime : (Nat.card X).Prime := IsSimpleGroup.prime_card
  have hx := sylow_dvd_of_order hadm hM
  rw [← pow_mul] at hx
  rcases (Nat.dvd_prime hprime).1 hx with h1 | h1
  · have hp2 := hadm.1.two_le
    have : p ^ (f * lieSylowExponent t n) ≥ p ^ 2 := Nat.pow_le_pow_right (by omega) hN
    have : p ^ 2 ≥ 4 := by nlinarith
    omega
  · rw [h1] at hx
    exact Nat.Prime.not_prime_pow hN (h1 ▸ hprime)

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs in
theorem not_typeL2_of_lieModel (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (ht : t ≠ .Tits) (hA : ¬ (t = .PSL ∧ n = 2)) (hZ : Subgroup.center X = ⊥) {r : ℕ}
    (hr : 10 ≤ r) : ¬ IsTypeL2 r X := by
  intro hT
  obtain ⟨hfin, hM, -⟩ := hO X t n p f hadm hX
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card X hT
  have hcard : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
    rw [hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv
  exact lie_order_ne_l2 hadm ht hA hM hr (fun h => by rw [← hcard]; exact hodd h)
    (fun h => by rw [← hcard]; exact (heven h).1)

end CFSG.HardMathSupport.Dickson.Sec6.I923
