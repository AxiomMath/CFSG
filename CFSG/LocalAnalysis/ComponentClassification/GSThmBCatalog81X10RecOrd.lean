module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

namespace X10Rec

theorem prod_lt_pow_sum {s : Finset ℕ} (hs : s.Nonempty) {Q : ℕ} (g e : ℕ → ℕ)
    (hg : ∀ i ∈ s, 0 < g i ∧ g i < Q ^ e i) : ∏ i ∈ s, g i < Q ^ (∑ i ∈ s, e i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_lt_prod_of_nonempty₀ (fun i hi => (hg i hi).1) (fun i hi => (hg i hi).2) hs

theorem pow_sub_one_pos {Q i : ℕ} (hQ : 2 ≤ Q) (hi : 1 ≤ i) : 0 < Q ^ i - 1 := by
  have : 2 ≤ Q ^ i := le_trans hQ (Nat.le_self_pow (by omega) Q)
  omega

theorem pow_sub_one_lt {Q i : ℕ} (hQ : 2 ≤ Q) : Q ^ i - 1 < Q ^ i := by
  have : 0 < Q ^ i := pow_pos (by omega) i
  omega

theorem pow_add_one_lt {Q i : ℕ} (hQ : 2 ≤ Q) (hi : 1 ≤ i) : Q ^ i + 1 < Q ^ (i + 1) := by
  have h2 : 2 ≤ Q ^ i := le_trans hQ (Nat.le_self_pow (by omega) Q)
  rw [pow_succ]
  nlinarith

theorem sum_Icc_le {a b B : ℕ} (e : ℕ → ℕ) (h : ∀ i ∈ Finset.Icc a b, e i ≤ B) :
    ∑ i ∈ Finset.Icc a b, e i ≤ (b + 1 - a) * B := by
  have := Finset.sum_le_card_nsmul (Finset.Icc a b) e B h
  rwa [Nat.card_Icc, smul_eq_mul] at this

theorem two_mul_choose (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)

theorem cofactor_psl_lt {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 2 ≤ n) :
    ∏ i ∈ Finset.Icc 2 n, (Q ^ i - 1) < Q ^ (3 * (n * (n - 1) / 2)) := by
  have hne : (Finset.Icc 2 n).Nonempty := ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  refine lt_of_lt_of_le (prod_lt_pow_sum hne _ (fun i => i) fun i hi =>
    ⟨pow_sub_one_pos hQ (by have := (Finset.mem_Icc.mp hi).1; omega), pow_sub_one_lt hQ⟩)
    (Nat.pow_le_pow_right (by omega) ?_)
  have h1 := sum_Icc_le (a := 2) (b := n) (B := n) (fun i => i)
    fun i hi => (Finset.mem_Icc.mp hi).2
  have h2 := two_mul_choose n
  have h3 : (n + 1 - 2) * n = n * (n - 1) := by
    rw [show n + 1 - 2 = n - 1 by omega, mul_comm]
  omega

theorem cofactor_psu_lt {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 3 ≤ n) :
    ∏ i ∈ Finset.Icc 2 n, (if Even i then Q ^ i - 1 else Q ^ i + 1) <
      Q ^ (3 * (n * (n - 1) / 2)) := by
  have hne : (Finset.Icc 2 n).Nonempty := ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  refine lt_of_lt_of_le (prod_lt_pow_sum hne _ (fun i => i + 1) fun i hi => ?_)
    (Nat.pow_le_pow_right (by omega) ?_)
  · have hi1 : 1 ≤ i := by have := (Finset.mem_Icc.mp hi).1; omega
    split_ifs
    · exact ⟨pow_sub_one_pos hQ hi1, lt_of_lt_of_le (pow_sub_one_lt hQ)
        (Nat.pow_le_pow_right (by omega) (by omega))⟩
    · exact ⟨by positivity, pow_add_one_lt hQ hi1⟩
  · have h1 := sum_Icc_le (a := 2) (b := n) (B := n + 1) (fun i => i + 1)
      fun i hi => by have := (Finset.mem_Icc.mp hi).2; omega
    have h2 := two_mul_choose n
    have h3 : 2 * ((n + 1 - 2) * (n + 1)) ≤ 3 * (n * (n - 1)) := by
      rw [show n + 1 - 2 = n - 1 by omega]
      have := Nat.mul_le_mul_left (n - 1) (show 2 * (n + 1) ≤ 3 * n by omega)
      nlinarith
    omega

theorem prod_sp_lt {Q m : ℕ} (hQ : 2 ≤ Q) (hm : 1 ≤ m) :
    ∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1) < Q ^ (2 * m * m) := by
  have hne : (Finset.Icc 1 m).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩⟩
  refine lt_of_lt_of_le (prod_lt_pow_sum hne _ (fun i => 2 * i) fun i hi =>
    ⟨pow_sub_one_pos hQ (by have := (Finset.mem_Icc.mp hi).1; omega), pow_sub_one_lt hQ⟩)
    (Nat.pow_le_pow_right (by omega) ?_)
  have h1 := sum_Icc_le (a := 1) (b := m) (B := 2 * m) (fun i => 2 * i)
    fun i hi => by have := (Finset.mem_Icc.mp hi).2; omega
  rw [show m + 1 - 1 = m by omega] at h1
  nlinarith

theorem cofactor_sp_lt {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 1 ≤ n) :
    ∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1) < Q ^ (3 * n ^ 2) :=
  lt_of_lt_of_le (prod_sp_lt hQ hn) (Nat.pow_le_pow_right (by omega) (by nlinarith))

theorem cofactor_plus_lt {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 2 ≤ n) :
    (Q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1) < Q ^ (3 * (n * (n - 1))) := by
  have h1 := Nat.mul_lt_mul'' (pow_sub_one_lt (i := n) hQ) (prod_sp_lt hQ (m := n - 1) (by omega))
  refine lt_of_lt_of_le h1 ?_
  rw [← pow_add]
  refine Nat.pow_le_pow_right (by omega) ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  nlinarith

theorem cofactor_minus_lt {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 2 ≤ n) :
    (Q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1) < Q ^ (3 * (n * (n - 1))) := by
  have h1 := Nat.mul_lt_mul'' (pow_add_one_lt (i := n) hQ (by omega))
    (prod_sp_lt hQ (m := n - 1) (by omega))
  refine lt_of_lt_of_le h1 ?_
  rw [← pow_add]
  refine Nat.pow_le_pow_right (by omega) ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  nlinarith

theorem mul_lt_pow {Q a b k m : ℕ} (ha : a < Q ^ k) (hb : b < Q ^ m) : a * b < Q ^ (k + m) := by
  rw [pow_add]
  exact Nat.mul_lt_mul'' ha hb

theorem triality_factor_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 8 + Q ^ 4 + 1 < Q ^ 9 := by
  have h4 : 2 ≤ Q ^ 4 := le_trans hQ (Nat.le_self_pow (by norm_num) Q)
  have h8 : Q ^ 8 = Q ^ 4 * Q ^ 4 := by rw [← pow_add]
  have h9 : Q ^ 9 = Q * Q ^ 8 := by rw [← pow_succ']
  rw [h9, h8]
  nlinarith

theorem lieOrderCofactor_lt {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hp2 : p ≠ 2) :
    lieOrderCofactor t n (p ^ f) < (p ^ f) ^ (3 * lieSylowExponent t n) := by
  have hQ : 2 ≤ p ^ f := le_trans hadm.1.two_le (Nat.le_self_pow (by have := hadm.2.1; omega) p)
  set Q := p ^ f with hQdef
  have s1 : ∀ k, Q ^ k - 1 < Q ^ k := fun k => pow_sub_one_lt hQ
  have a1 : ∀ k, 1 ≤ k → Q ^ k + 1 < Q ^ (k + 1) := fun k hk => pow_add_one_lt hQ hk
  have mono : ∀ a b : ℕ, a ≤ b → Q ^ a ≤ Q ^ b := fun a b h => Nat.pow_le_pow_right (by omega) h
  cases t with
  | PSL => exact cofactor_psl_lt hQ hadm.2.2.1
  | PSU => exact cofactor_psu_lt hQ hadm.2.2.1
  | PSp => exact cofactor_sp_lt hQ (by have := hadm.2.2.1; omega)
  | POmegaOdd => exact cofactor_sp_lt hQ (by have := hadm.2.2.1; omega)
  | POmegaPlus => exact cofactor_plus_lt hQ (by have := hadm.2.2; omega)
  | POmegaMinus => exact cofactor_minus_lt hQ (by have := hadm.2.2; omega)
  | G2 => exact lt_of_lt_of_le (mul_lt_pow (s1 6) (s1 2)) (mono _ _ (by simp [lieSylowExponent]))
  | F4 =>
    exact lt_of_lt_of_le (mul_lt_pow (mul_lt_pow (mul_lt_pow (s1 12) (s1 8)) (s1 6)) (s1 2))
      (mono _ _ (by simp [lieSylowExponent]))
  | E6 =>
    exact lt_of_lt_of_le (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow (s1 12)
      (s1 9)) (s1 8)) (s1 6)) (s1 5)) (s1 2)) (mono _ _ (by simp [lieSylowExponent]))
  | E7 =>
    exact lt_of_lt_of_le (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow
      (mul_lt_pow (s1 18) (s1 14)) (s1 12)) (s1 10)) (s1 8)) (s1 6)) (s1 2))
      (mono _ _ (by simp [lieSylowExponent]))
  | E8 =>
    exact lt_of_lt_of_le (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow
      (mul_lt_pow (mul_lt_pow (s1 30) (s1 24)) (s1 20)) (s1 18)) (s1 14)) (s1 12)) (s1 8))
      (s1 2)) (mono _ _ (by simp [lieSylowExponent]))
  | twistedE6 =>
    exact lt_of_lt_of_le (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow (mul_lt_pow (s1 12)
      (a1 9 (by norm_num))) (s1 8)) (s1 6)) (a1 5 (by norm_num))) (s1 2))
      (mono _ _ (by simp [lieSylowExponent]))
  | trialityD4 =>
    exact lt_of_lt_of_le (mul_lt_pow (mul_lt_pow (triality_factor_lt hQ) (s1 6)) (s1 2))
      (mono _ _ (by simp [lieSylowExponent]))
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedG2 =>
    have h1 : Q - 1 < Q ^ 1 := by rw [pow_one]; omega
    exact lt_of_lt_of_le (mul_lt_pow (a1 3 (by norm_num)) h1)
      (mono _ _ (by simp [lieSylowExponent]))
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

theorem two_mul_pow_eight_lt {q : ℕ} (hq : 5 ≤ q) :
    2 * (q + 1) ^ 8 < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have h2 : 25 ≤ q ^ 2 := by nlinarith
  have h4 : 625 ≤ q ^ 4 := by
    have : q ^ 4 = q ^ 2 * q ^ 2 := by rw [← pow_add]
    nlinarith
  have e2 : 25 * (q ^ 2 - 1) ≥ 24 * q ^ 2 := by omega
  have e4 : 625 * (q ^ 4 - 1) ≥ 624 * q ^ 4 := by omega
  have e1 : 25 * (q + 1) ^ 2 ≤ 36 * q ^ 2 := by nlinarith
  have e8 : 25 ^ 4 * (q + 1) ^ 8 ≤ 36 ^ 4 * q ^ 8 := by
    have := Nat.pow_le_pow_left e1 4
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at this
    exact this
  have eL : 25 * 625 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) ≥ 24 * 624 * q ^ 10 := by
    have := Nat.mul_le_mul e2 e4
    have h10 : q ^ 10 = q ^ 4 * (q ^ 2 * q ^ 4) := by rw [← pow_add, ← pow_add]
    rw [h10]
    nlinarith
  have hq8 : 25 * q ^ 8 ≤ q ^ 10 := by
    have : q ^ 10 = q ^ 2 * q ^ 8 := by rw [← pow_add]
    rw [this]
    exact Nat.mul_le_mul_right _ h2
  nlinarith

theorem ordProj_eq_one {s n : ℕ} (h : ¬ s ∣ n) : s ^ n.factorization s = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero]

theorem ordProj_sp4_le {q s : ℕ} (hq : 2 ≤ q) (hs : s.Prime) (hs2 : s ≠ 2) (hsq : ¬ s ∣ q) :
    s ^ (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))).factorization s ≤ (q + 1) ^ 2 := by
  have e2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q := by omega
    zify [this, Nat.one_le_pow 2 q (by omega)]
    ring
  have e4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
    zify [this, Nat.one_le_pow 4 q (by omega)]
    ring
  have hA : q - 1 ≠ 0 := by omega
  have hB : q + 1 ≠ 0 := by omega
  have hC : q ^ 2 + 1 ≠ 0 := by positivity
  have hQ4 : q ^ 4 ≠ 0 := by positivity
  have hs4 : ¬ s ∣ q ^ 4 := fun h => hsq (hs.dvd_of_dvd_pow h)
  have hnot2 : ¬ s ∣ 2 := fun h => hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp h)
  have hval : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) =
      q ^ 4 * (((q - 1) * (q + 1)) * ((q - 1) * (q + 1)) * (q ^ 2 + 1)) := by
    rw [e4, e2]; ring
  rw [hval, Nat.ordProj_mul s hQ4 (by positivity), ordProj_eq_one hs4, one_mul,
    Nat.ordProj_mul s (by positivity) hC, Nat.ordProj_mul s (by positivity) (by positivity),
    Nat.ordProj_mul s hA hB]
  by_cases hsC : s ∣ q ^ 2 + 1
  · have hsA : ¬ s ∣ q - 1 := fun h => hnot2 (by
      have h1 : s ∣ (q - 1) * (q + 1) := dvd_mul_of_dvd_left h _
      rw [← e2] at h1
      have h2 : q ^ 2 + 1 = (q ^ 2 - 1) + 2 := by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
        omega
      rw [h2] at hsC
      exact (Nat.dvd_add_right h1).mp hsC)
    have hsB : ¬ s ∣ q + 1 := fun h => hnot2 (by
      have h1 : s ∣ (q - 1) * (q + 1) := dvd_mul_of_dvd_right h _
      rw [← e2] at h1
      have h2 : q ^ 2 + 1 = (q ^ 2 - 1) + 2 := by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
        omega
      rw [h2] at hsC
      exact (Nat.dvd_add_right h1).mp hsC)
    rw [ordProj_eq_one hsA, ordProj_eq_one hsB, mul_one, one_mul, one_mul]
    calc s ^ (q ^ 2 + 1).factorization s ≤ q ^ 2 + 1 := Nat.ordProj_le s hC
      _ ≤ (q + 1) ^ 2 := by nlinarith
  · rw [ordProj_eq_one hsC, mul_one]
    have hAB : ¬ (s ∣ q - 1 ∧ s ∣ q + 1) := fun ⟨h1, h2⟩ => hnot2 (by
      have : q + 1 = (q - 1) + 2 := by omega
      rw [this] at h2
      exact (Nat.dvd_add_right h1).mp h2)
    have hle : s ^ (q - 1).factorization s * s ^ (q + 1).factorization s ≤ q + 1 := by
      by_cases h1 : s ∣ q - 1
      · have h2 : ¬ s ∣ q + 1 := fun h2 => hAB ⟨h1, h2⟩
        rw [ordProj_eq_one h2, mul_one]
        exact (Nat.ordProj_le s hA).trans (by omega)
      · rw [ordProj_eq_one h1, one_mul]
        exact Nat.ordProj_le s hB
    calc s ^ (q - 1).factorization s * s ^ (q + 1).factorization s *
          (s ^ (q - 1).factorization s * s ^ (q + 1).factorization s) ≤ (q + 1) * (q + 1) :=
          Nat.mul_le_mul hle hle
      _ = (q + 1) ^ 2 := by ring

theorem card_lt_ordProj_pow_four (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) :
    Nat.card X < (p ^ (Nat.card X).factorization p) ^ 4 := by
  obtain ⟨-, hord, hfac⟩ := hO X t n p f hadm hX
  rw [hfac]
  have hdiv : 0 < lieOrderDivisor t n (p ^ f) :=
    Nat.pos_of_ne_zero (lieOrderDivisor_ne_zero hadm)
  have hle : Nat.card X ≤ lieOrderNumerator t n (p ^ f) := by
    rw [← hord]
    exact Nat.le_mul_of_pos_right _ hdiv
  rw [lieOrderNumerator_eq hadm] at hle
  have hlt := lieOrderCofactor_lt hadm hp2
  have hpos : 0 < (p ^ f) ^ lieSylowExponent t n := pow_pos (pow_pos hadm.1.pos f) _
  calc Nat.card X ≤ (p ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (p ^ f) := hle
    _ < (p ^ f) ^ lieSylowExponent t n * (p ^ f) ^ (3 * lieSylowExponent t n) :=
        Nat.mul_lt_mul_of_pos_left hlt hpos
    _ = (p ^ (lieSylowExponent t n * f)) ^ 4 := by
        rw [← pow_add, ← pow_mul, ← pow_mul]
        ring_nf

theorem char_eq_of_card_psp (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n r f' p f : ℕ} (hr2 : r ≠ 2) (hadm : StatedLieAdmissible t n r f')
    (hX : Blueprint.LieModel X t n r f') (hp : p.Prime) (h5 : 5 ≤ p ^ f)
    (hcard : Nat.card X * 2 = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1))) :
    r = p := by
  by_contra hrp
  have hr := hadm.1
  have hlt := card_lt_ordProj_pow_four hO hr2 hadm hX
  have hX0 : Nat.card X ≠ 0 := fun h => by
    rw [h, zero_mul] at hcard
    have := two_mul_pow_eight_lt h5
    omega
  have hfac : (Nat.card X * 2).factorization r = (Nat.card X).factorization r := by
    rw [Nat.factorization_mul hX0 two_ne_zero, Finsupp.add_apply,
      Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply, ite_eq_right_iff.mpr
        (fun h => absurd h.symm hr2), add_zero]
  have hrq : ¬ r ∣ p ^ f := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp
    (hr.dvd_of_dvd_pow h))
  have hle := ordProj_sp4_le (q := p ^ f) (by omega) hr hr2 hrq
  rw [← hcard, hfac] at hle
  have h8 : Nat.card X < (p ^ f + 1) ^ 8 := by
    calc Nat.card X < (r ^ (Nat.card X).factorization r) ^ 4 := hlt
      _ ≤ ((p ^ f + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left hle 4
      _ = (p ^ f + 1) ^ 8 := by rw [← pow_mul]
  have := two_mul_pow_eight_lt h5
  omega

theorem card_M11_dvd : Nat.card ↥CFSG.Blueprint.NativeSporadic.M11 ∣ 39916800 := by
  have h := Subgroup.card_subgroup_dvd_card CFSG.Blueprint.NativeSporadic.M11
  rw [Nat.card_perm, Nat.card_fin] at h
  exact h

theorem not_pow_four_dvd {q : ℕ} (h5 : 5 ≤ q) (hodd : q % 2 = 1) : ¬ q ^ 4 ∣ 39916800 := by
  intro h
  have hle : q ^ 4 ≤ 39916800 := Nat.le_of_dvd (by norm_num) h
  have hq : q ≤ 80 := by
    by_contra hq
    have : 81 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  interval_cases q <;> omega

end X10Rec

end CFSG.ComponentClassification.GSThmB
