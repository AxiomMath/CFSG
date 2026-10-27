module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

private theorem three_pow_odd_mod_sixteen (m : ℕ) :
    3 ^ (2 * m + 1) % 16 = 3 ∨ 3 ^ (2 * m + 1) % 16 = 11 := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    have : 3 ^ (2 * (k + 1) + 1) = 9 * 3 ^ (2 * k + 1) := by ring
    omega

theorem orderRee_mod_sixteen (m : ℕ) : orderRee (3 ^ (2 * m + 1)) % 16 = 8 := by
  have hq := three_pow_odd_mod_sixteen m
  generalize 3 ^ (2 * m + 1) = q at hq ⊢
  unfold orderRee
  rcases hq with hq | hq
  · have h1 : (q - 1) % 16 = 2 := by omega
    have h2 : q ^ 3 % 16 = 11 := by rw [Nat.pow_mod, hq]
    have h3 : (q ^ 3 + 1) % 16 = 12 := by omega
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), h2, h3, h1]
  · have h1 : (q - 1) % 16 = 10 := by omega
    have h2 : q ^ 3 % 16 = 3 := by rw [Nat.pow_mod, hq]
    have h3 : (q ^ 3 + 1) % 16 = 4 := by omega
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), h2, h3, h1]

private theorem pow_six_le_orderRee {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 6 ≤ orderRee Q := by
  unfold orderRee
  calc Q ^ 6 = Q ^ 3 * Q ^ 3 * 1 := by ring
    _ ≤ Q ^ 3 * (Q ^ 3 + 1) * (Q - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.le_succ _)) (by omega)

theorem orderRee_ge {m : ℕ} (hm : 1 ≤ m) : 387420489 ≤ orderRee (3 ^ (2 * m + 1)) := by
  have h27 : 27 ≤ 3 ^ (2 * m + 1) := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 387420489 = 27 ^ 6 := by norm_num
    _ ≤ (3 ^ (2 * m + 1)) ^ 6 := Nat.pow_le_pow_left h27 6
    _ ≤ _ := pow_six_le_orderRee (by omega)

theorem orderRee_eq_three_pow_mul (m : ℕ) :
    orderRee (3 ^ (2 * m + 1)) = 3 ^ (3 * (2 * m + 1)) *
        (((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1)) ∧
      ¬ 3 ∣ ((3 ^ (2 * m + 1)) ^ 3 + 1) * (3 ^ (2 * m + 1) - 1) := by
  refine ⟨by unfold orderRee; rw [mul_assoc, ← pow_mul, mul_comm (2 * m + 1) 3], ?_⟩
  obtain ⟨t, ht⟩ : 3 ∣ 3 ^ (2 * m + 1) := dvd_pow_self 3 (by omega)
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at ht
      exact absurd ht (pow_ne_zero _ (by norm_num))
    · exact h
  rw [ht]
  have h1 : (3 * t) ^ 3 + 1 = 3 * (9 * t ^ 3) + 1 := by ring
  rw [h1]
  intro h
  have hm1 : (3 * (9 * t ^ 3) + 1) % 3 = 1 := by omega
  have hm2 : (3 * t - 1) % 3 = 2 := by omega
  have := Nat.mod_eq_zero_of_dvd h
  rw [Nat.mul_mod, hm1, hm2] at this
  exact absurd this (by norm_num)

private theorem eq_of_prime_pow_mul_eq {p a b x y : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : p ^ a * x = p ^ b * y) : a = b := by
  have key : ∀ c z : ℕ, ¬ p ∣ z → (p ^ c * z).factorization p = c := by
    intro c z hpz
    have hz : z ≠ 0 := by
      rintro rfl
      exact hpz (dvd_zero p)
    rw [Nat.factorization_mul (pow_ne_zero c hp.ne_zero) hz, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpz,
      add_zero]
  have h' : (p ^ a * x).factorization p = (p ^ b * y).factorization p := by rw [h]
  rwa [key a x hx, key b y hy] at h'

private theorem not_dvd_three_pow {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (k : ℕ) : ¬ r ∣ 3 ^ k := by
  intro h
  exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h))

private theorem le_sq_of_prime_pow_dvd_orderRee {r a m : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : r ^ a ∣ orderRee (3 ^ (2 * m + 1))) : r ^ a ≤ (3 ^ (2 * m + 1)) ^ 2 := by
  have hrQ : ¬ r ∣ 3 ^ (2 * m + 1) := not_dvd_three_pow hr hr3 _
  have hQ3 : 3 ≤ 3 ^ (2 * m + 1) :=
    (le_of_eq (pow_one 3).symm).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  generalize 3 ^ (2 * m + 1) = Q at hrQ hQ3 h ⊢
  obtain ⟨R, rfl⟩ : ∃ R, Q = R + 1 := ⟨Q - 1, by omega⟩
  have hR : 2 ≤ R := by omega
  have hN : orderRee (R + 1) = (R + 1) ^ 3 * (R + 2) * (R ^ 2 + R + 1) * R := by
    unfold orderRee
    rw [Nat.add_sub_cancel]
    ring
  rw [hN] at h
  have hcop : ∀ z : ℕ, ¬ r ∣ z → Nat.Coprime (r ^ a) z := fun z hz =>
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr).2 hz)
  have hQ3' : ¬ r ∣ (R + 1) ^ 3 := fun h' => hrQ (hr.dvd_of_dvd_pow h')
  have hAB : r ∣ R + 2 → ¬ r ∣ R := fun hA hB => by
    have : r ∣ 2 := (Nat.dvd_add_right hB).1 hA
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 this)
  have hAC : r ∣ R + 2 → ¬ r ∣ R ^ 2 + R + 1 := fun hA hC => by
    have he : R ^ 2 + R + 1 = (R + 2) * (R - 1) + 3 := by
      obtain ⟨S, rfl⟩ : ∃ S, R = S + 1 := ⟨R - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    rw [he] at hC
    have : r ∣ 3 := (Nat.dvd_add_right (Dvd.dvd.mul_right hA _)).1 hC
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this)
  have hBC : r ∣ R → ¬ r ∣ R ^ 2 + R + 1 := fun hB hC => by
    have he : R ^ 2 + R + 1 = R * (R + 1) + 1 := by ring
    rw [he] at hC
    have : r ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_right hB _)).1 hC
    exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  have hsq : (R + 1) ^ 2 = R ^ 2 + R + 1 + R := by ring
  by_cases hA : r ∣ R + 2
  · have hdvd : r ^ a ∣ R + 2 := by
      refine (hcop ((R + 1) ^ 3 * (R ^ 2 + R + 1) * R) ?_).dvd_of_dvd_mul_right ?_
      · intro h'
        rcases (Nat.Prime.dvd_mul hr).1 h' with h' | h'
        · rcases (Nat.Prime.dvd_mul hr).1 h' with h' | h'
          · exact hQ3' h'
          · exact hAC hA h'
        · exact hAB hA h'
      · have : (R + 1) ^ 3 * (R + 2) * (R ^ 2 + R + 1) * R =
            (R + 2) * ((R + 1) ^ 3 * (R ^ 2 + R + 1) * R) := by ring
        rwa [this] at h
    have := Nat.le_of_dvd (by omega) hdvd
    nlinarith
  · by_cases hB : r ∣ R
    · have hdvd : r ^ a ∣ R := by
        refine (hcop ((R + 1) ^ 3 * (R + 2) * (R ^ 2 + R + 1)) ?_).dvd_of_dvd_mul_left h
        intro h'
        rcases (Nat.Prime.dvd_mul hr).1 h' with h' | h'
        · rcases (Nat.Prime.dvd_mul hr).1 h' with h' | h'
          · exact hQ3' h'
          · exact hA h'
        · exact hBC hB h'
      have := Nat.le_of_dvd (by omega) hdvd
      nlinarith
    · have hdvd : r ^ a ∣ R ^ 2 + R + 1 := by
        refine (hcop ((R + 1) ^ 3 * (R + 2) * R) ?_).dvd_of_dvd_mul_right ?_
        · intro h'
          rcases (Nat.Prime.dvd_mul hr).1 h' with h' | h'
          · rcases (Nat.Prime.dvd_mul hr).1 h' with h' | h'
            · exact hQ3' h'
            · exact hA h'
          · exact hB h'
        · have : (R + 1) ^ 3 * (R + 2) * (R ^ 2 + R + 1) * R =
              (R ^ 2 + R + 1) * ((R + 1) ^ 3 * (R + 2) * R) := by ring
          rwa [this] at h
      have := Nat.le_of_dvd (by positivity) hdvd
      omega

theorem not_lie_char_of_card_ree (hb : LieOrderBridge) {T : Type} [Group T] [Finite T] {m r : ℕ}
    (hm : 1 ≤ m) (hT : Nat.card T = orderRee (3 ^ (2 * m + 1))) (hr : r.Prime) (hr3 : r ≠ 3) :
    ¬ catalogIs T (onLie fun d => d.characteristic = r) := by
  have hbig := orderRee_ge hm
  by_cases hr2 : r = 2
  · subst hr2
    have h16 := orderRee_mod_sixteen m
    refine I1416QRows.not_lie_char_of_card hb Nat.prime_two (a := 3)
      (m := orderRee (3 ^ (2 * m + 1)) / 8) ?_ ?_ ?_
    · rw [hT, show (2 : ℕ) ^ 3 = 8 from rfl]
      omega
    · omega
    · rw [show (2 : ℕ) ^ (2 * 3) = 64 from rfl]
      omega
  · set N := orderRee (3 ^ (2 * m + 1)) with hNdef
    have hN0 : N ≠ 0 := by omega
    set a := N.factorization r with ha
    have hdvd : r ^ a ∣ N := Nat.ordProj_dvd N r
    have hle := le_sq_of_prime_pow_dvd_orderRee hr hr2 hr3 hdvd
    have hcube : r ^ a * r ^ a * r ^ a ≤ N := by
      have h6 : ((3 ^ (2 * m + 1)) ^ 2) ^ 3 ≤ N := by
        rw [← pow_mul]
        exact pow_six_le_orderRee (by
          calc 2 ≤ 3 ^ 1 := by norm_num
            _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
      calc r ^ a * r ^ a * r ^ a = (r ^ a) ^ 3 := by ring
        _ ≤ ((3 ^ (2 * m + 1)) ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
        _ ≤ N := h6
    refine I1416QRows.not_lie_char_of_card hb hr (a := a) (m := N / r ^ a) ?_
      (Nat.not_dvd_ordCompl hr hN0) ?_
    · rw [hT]
      exact (Nat.ordProj_mul_ordCompl_eq_self N r).symm
    · rw [Nat.le_div_iff_mul_le (pow_pos hr.pos a), two_mul, pow_add]
      exact hcube

private theorem eight_dvd_pow_two_mul_sub_one {Q : ℕ} (hQ : Odd Q) (k : ℕ) : 8 ∣ Q ^ (2 * k) - 1 := by
  exact (Nat.eight_dvd_sq_sub_one_of_odd hQ).trans (Nat.pow_sub_one_dvd_pow_sub_one Q (dvd_mul_right 2 k))

private theorem sixteen_dvd_pow_four_mul_sub_one {Q : ℕ} (hQ : Odd Q) {k : ℕ} (hk : 1 ≤ k) :
    16 ∣ Q ^ (4 * k) - 1 := by
  have h4 : 16 ∣ Q ^ 4 - 1 := by
    have hQ1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ.pos
    have hsplit : Q ^ 4 - 1 = (Q ^ 2 - 1) * (Q ^ 2 + 1) := by
      have : Q ^ 4 = Q ^ 2 * Q ^ 2 := by ring
      rw [this]
      obtain ⟨u, hu⟩ : ∃ u, Q ^ 2 = u + 1 := ⟨Q ^ 2 - 1, by omega⟩
      rw [hu, Nat.add_sub_cancel]
      ring_nf
      omega
    rw [hsplit]
    have h2 : 2 ∣ Q ^ 2 + 1 := (hQ.pow.add_one).two_dvd
    exact dvd_trans (by norm_num : (16 : ℕ) ∣ 8 * 2) (Nat.mul_dvd_mul (Nat.eight_dvd_sq_sub_one_of_odd hQ) h2)
  exact h4.trans (Nat.pow_sub_one_dvd_pow_sub_one Q (dvd_mul_right 4 k))

private theorem thirtytwo_dvd_pow_eight_sub_one {Q : ℕ} (hQ : Odd Q) : 32 ∣ Q ^ 8 - 1 := by
  have h16 : 16 ∣ Q ^ 4 - 1 := by simpa using sixteen_dvd_pow_four_mul_sub_one hQ (le_refl 1)
  have hQ1 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ.pos
  have hsplit : Q ^ 8 - 1 = (Q ^ 4 - 1) * (Q ^ 4 + 1) := by
    have : Q ^ 8 = Q ^ 4 * Q ^ 4 := by ring
    rw [this]
    obtain ⟨u, hu⟩ : ∃ u, Q ^ 4 = u + 1 := ⟨Q ^ 4 - 1, by omega⟩
    rw [hu, Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hsplit]
  exact dvd_trans (by norm_num : (32 : ℕ) ∣ 16 * 2)
    (Nat.mul_dvd_mul h16 (hQ.pow.add_one).two_dvd)

private theorem two_dvd_pow_sub_one {Q : ℕ} (hQ : Odd Q) (i : ℕ) : 2 ∣ Q ^ i - 1 :=
  (Nat.Odd.sub_odd hQ.pow odd_one).two_dvd

private theorem two_dvd_pow_add_one {Q : ℕ} (hQ : Odd Q) (i : ℕ) : 2 ∣ Q ^ i + 1 :=
  (hQ.pow.add_one).two_dvd

private theorem sixtyfour_dvd_two_four {Q : ℕ} (hQ : Odd Q) :
    64 ∣ (Q ^ (2 * 1) - 1) * (Q ^ (2 * 2) - 1) :=
  dvd_trans (by norm_num : (64 : ℕ) ∣ 8 * 8) (Nat.mul_dvd_mul (eight_dvd_pow_two_mul_sub_one hQ 1)
    (eight_dvd_pow_two_mul_sub_one hQ 2))

private theorem sixteen_dvd_div {N g : ℕ} (h : g * 16 ∣ N) : 16 ∣ N / g :=
  Nat.dvd_div_of_mul_dvd h

private theorem card_facts_of_char_three {q : TauCeti.PrimePower} (hq : q.p = 3) :
    Odd q.card ∧ 3 ∣ q.card ∧ 3 ≤ q.card := by
  rw [TauCeti.PrimePower.card_def, hq]
  refine ⟨Odd.pow (by decide), dvd_pow_self 3 q.exponent_pos.ne', ?_⟩
  calc 3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos

theorem sixteen_dvd_lieOrderFormula {e : TauCeti.LieTypeIndex} (hv : e.Valid)
    (he : e.characteristic = 3) (hA1 : ∀ q, e ≠ .A 1 q) (hR : ∀ k, e ≠ .reeG2 k) :
    16 ∣ lieOrderFormula e := by
  have hs : e.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff e).1 hv).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A n q =>
    obtain ⟨hQ, h3, -⟩ := card_facts_of_char_three (by simpa using he)
    have hn1 : 1 ≤ n := hs.1
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · have : n = 1 := by omega
        exact (hA1 q (by rw [this])).elim
      · exact h
    simp only [lieOrderFormula, orderA]
    apply sixteen_dvd_div
    set Q := q.card
    by_cases hn : n = 2
    · subst hn
      have hg : Nat.gcd (2 + 1) (Q - 1) ∣ 3 := Nat.gcd_dvd_left _ _
      have h16 : 16 ∣ ∏ i ∈ Finset.Icc 2 (2 + 1), (Q ^ i - 1) := by
        have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (2 + 1) := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          simp only [Finset.mem_Icc]
          omega
        refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
        rw [Finset.prod_pair (by norm_num)]
        exact dvd_trans (by norm_num : (16 : ℕ) ∣ 8 * 2)
          (Nat.mul_dvd_mul (Nat.eight_dvd_sq_sub_one_of_odd hQ) (two_dvd_pow_sub_one hQ 3))
      have h48 : 3 * 16 ∣ Q ^ (2 * (2 + 1) / 2) * ∏ i ∈ Finset.Icc 2 (2 + 1), (Q ^ i - 1) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
          (Dvd.dvd.mul_right (h3.trans (dvd_pow_self Q (by norm_num))) _)
          (Dvd.dvd.mul_left h16 _)
      exact (Nat.mul_dvd_mul_right hg 16).trans h48
    ·
      have hg : Nat.gcd (n + 1) (Q - 1) ∣ Q - 1 := Nat.gcd_dvd_right _ _
      have hsub : ({2, 4} : Finset ℕ) ⊆ Finset.Icc 2 (n + 1) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        simp only [Finset.mem_Icc]
        omega
      have hprod : (Q - 1) * 16 ∣ ∏ i ∈ Finset.Icc 2 (n + 1), (Q ^ i - 1) := by
        refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
        rw [Finset.prod_pair (by norm_num)]
        exact Nat.mul_dvd_mul (CFSG.HardMathSupport.Solomon.Coordinator.I1420.sub_one_dvd_sq_sub_one Q)
          (by simpa using sixteen_dvd_pow_four_mul_sub_one hQ (le_refl 1))
      exact (Nat.mul_dvd_mul_right hg 16).trans (Dvd.dvd.mul_left hprod _)
  | twistedA n q =>
    obtain ⟨hQ, h3, -⟩ := card_facts_of_char_three (by simpa using he)
    have hn2 : 2 ≤ n := hs.1
    simp only [lieOrderFormula, orderTwistedA]
    apply sixteen_dvd_div
    set Q := q.card
    by_cases hn : n = 2
    · subst hn
      have hg : Nat.gcd (2 + 1) (Q + 1) ∣ 3 := Nat.gcd_dvd_left _ _
      have h16 : 16 ∣ ∏ i ∈ Finset.Icc 2 (2 + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1) := by
        have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (2 + 1) := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          simp only [Finset.mem_Icc]
          omega
        refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
        rw [Finset.prod_pair (by norm_num)]
        have e2 : Even 2 := by decide
        have e3 : ¬ Even 3 := by decide
        simp only [e2, e3, ↓reduceIte]
        exact dvd_trans (by norm_num : (16 : ℕ) ∣ 8 * 2)
          (Nat.mul_dvd_mul (Nat.eight_dvd_sq_sub_one_of_odd hQ) (two_dvd_pow_add_one hQ 3))
      have h48 : 3 * 16 ∣ Q ^ (2 * (2 + 1) / 2) *
          ∏ i ∈ Finset.Icc 2 (2 + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1) :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
          (Dvd.dvd.mul_right (h3.trans (dvd_pow_self Q (by norm_num))) _)
          (Dvd.dvd.mul_left h16 _)
      exact (Nat.mul_dvd_mul_right hg 16).trans h48
    · have hg : Nat.gcd (n + 1) (Q + 1) ∣ Q + 1 := Nat.gcd_dvd_right _ _
      have hsub : ({2, 4} : Finset ℕ) ⊆ Finset.Icc 2 (n + 1) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        simp only [Finset.mem_Icc]
        omega
      have hprod : (Q + 1) * 16 ∣
          ∏ i ∈ Finset.Icc 2 (n + 1), (if Even i then Q ^ i - 1 else Q ^ i + 1) := by
        refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
        rw [Finset.prod_pair (by norm_num)]
        have e2 : Even 2 := by decide
        have e4 : Even 4 := by decide
        simp only [e2, e4, ↓reduceIte]
        exact Nat.mul_dvd_mul
          (CFSG.HardMathSupport.Solomon.Coordinator.I1420.add_one_dvd_sq_sub_one Q hQ.pos)
          (by simpa using sixteen_dvd_pow_four_mul_sub_one hQ (le_refl 1))
      exact (Nat.mul_dvd_mul_right hg 16).trans (Dvd.dvd.mul_left hprod _)
  | B n q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    have hn2 : 2 ≤ n := hs.1
    simp only [lieOrderFormula, orderBC]
    apply sixteen_dvd_div
    have hg : Nat.gcd 2 (q.card - 1) ∣ 2 := Nat.gcd_dvd_left _ _
    have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_Icc]
      omega
    have h64 : 64 ∣ ∏ i ∈ Finset.Icc 1 n, (q.card ^ (2 * i) - 1) := by
      refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
      rw [Finset.prod_pair (by norm_num)]
      exact sixtyfour_dvd_two_four hQ
    exact (Nat.mul_dvd_mul_right hg 16).trans ((by norm_num : 2 * 16 ∣ 64).trans
      (Dvd.dvd.mul_left h64 _))
  | C n q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    have hn2 : 2 ≤ n := by have := hs.1; omega
    simp only [lieOrderFormula, orderBC]
    apply sixteen_dvd_div
    have hg : Nat.gcd 2 (q.card - 1) ∣ 2 := Nat.gcd_dvd_left _ _
    have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_Icc]
      omega
    have h64 : 64 ∣ ∏ i ∈ Finset.Icc 1 n, (q.card ^ (2 * i) - 1) := by
      refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
      rw [Finset.prod_pair (by norm_num)]
      exact sixtyfour_dvd_two_four hQ
    exact (Nat.mul_dvd_mul_right hg 16).trans ((by norm_num : 2 * 16 ∣ 64).trans
      (Dvd.dvd.mul_left h64 _))
  | D n q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    have hn4 : 4 ≤ n := hs
    simp only [lieOrderFormula, orderD]
    apply sixteen_dvd_div
    have hg : Nat.gcd 4 (q.card ^ n - 1) ∣ 4 := Nat.gcd_dvd_left _ _
    have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 (n - 1) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_Icc]
      omega
    have h64 : 64 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q.card ^ (2 * i) - 1) := by
      refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
      rw [Finset.prod_pair (by norm_num)]
      exact sixtyfour_dvd_two_four hQ
    exact (Nat.mul_dvd_mul_right hg 16).trans ((by norm_num : 4 * 16 ∣ 64).trans
      (Dvd.dvd.mul_left h64 _))
  | twistedD n q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    have hn4 : 4 ≤ n := hs
    simp only [lieOrderFormula, orderTwistedD]
    apply sixteen_dvd_div
    have hg : Nat.gcd 4 (q.card ^ n + 1) ∣ 4 := Nat.gcd_dvd_left _ _
    have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 (n - 1) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_Icc]
      omega
    have h64 : 64 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q.card ^ (2 * i) - 1) := by
      refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
      rw [Finset.prod_pair (by norm_num)]
      exact sixtyfour_dvd_two_four hQ
    exact (Nat.mul_dvd_mul_right hg 16).trans ((by norm_num : 4 * 16 ∣ 64).trans
      (Dvd.dvd.mul_left h64 _))
  | E6 q =>
    obtain ⟨hQ, h3, -⟩ := card_facts_of_char_three (by simpa using he)
    simp only [lieOrderFormula, orderE6]
    apply sixteen_dvd_div
    have hg : Nat.gcd 3 (q.card - 1) ∣ 3 := Nat.gcd_dvd_left _ _
    have h16 : 16 ∣ q.card ^ 8 - 1 := by simpa using sixteen_dvd_pow_four_mul_sub_one hQ (k := 2) (by norm_num)
    refine (Nat.mul_dvd_mul_right hg 16).trans (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ ?_)
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (Dvd.dvd.mul_right (h3.trans (dvd_pow_self _ (by norm_num))) _) _) _) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h16 _) _) _) _
  | twistedE6 q =>
    obtain ⟨hQ, h3, -⟩ := card_facts_of_char_three (by simpa using he)
    simp only [lieOrderFormula, orderTwistedE6]
    apply sixteen_dvd_div
    have hg : Nat.gcd 3 (q.card + 1) ∣ 3 := Nat.gcd_dvd_left _ _
    have h16 : 16 ∣ q.card ^ 8 - 1 := by simpa using sixteen_dvd_pow_four_mul_sub_one hQ (k := 2) (by norm_num)
    refine (Nat.mul_dvd_mul_right hg 16).trans (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ ?_)
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
        (Dvd.dvd.mul_right (Dvd.dvd.mul_right (h3.trans (dvd_pow_self _ (by norm_num))) _) _) _) _) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h16 _) _) _) _
  | E7 q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    simp only [lieOrderFormula, orderE7]
    apply sixteen_dvd_div
    have hg : Nat.gcd 2 (q.card - 1) ∣ 2 := Nat.gcd_dvd_left _ _
    have h32 : 32 ∣ q.card ^ 8 - 1 := thirtytwo_dvd_pow_eight_sub_one hQ
    exact (Nat.mul_dvd_mul_right hg 16).trans ((by norm_num : 2 * 16 ∣ 32).trans
      (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h32 _) _) _))
  | E8 q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    simp only [lieOrderFormula, orderE8]
    have h16 : 16 ∣ q.card ^ 8 - 1 := by simpa using sixteen_dvd_pow_four_mul_sub_one hQ (k := 2) (by norm_num)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h16 _) _
  | F4 q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    simp only [lieOrderFormula, orderF4]
    have h16 : 16 ∣ q.card ^ 8 - 1 := by simpa using sixteen_dvd_pow_four_mul_sub_one hQ (k := 2) (by norm_num)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h16 _) _) _
  | G2 q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    simp only [lieOrderFormula, orderG2]
    have h64 : 8 * 8 ∣ (q.card ^ 6 - 1) * (q.card ^ 2 - 1) :=
      Nat.mul_dvd_mul (by simpa using eight_dvd_pow_two_mul_sub_one hQ 3) (Nat.eight_dvd_sq_sub_one_of_odd hQ)
    rw [mul_assoc]
    exact Dvd.dvd.mul_left ((by norm_num : (16 : ℕ) ∣ 8 * 8).trans h64) _
  | trialityD4 q =>
    obtain ⟨hQ, -, -⟩ := card_facts_of_char_three (by simpa using he)
    simp only [lieOrderFormula, orderTrialityD4]
    have h64 : 8 * 8 ∣ (q.card ^ 6 - 1) * (q.card ^ 2 - 1) :=
      Nat.mul_dvd_mul (by simpa using eight_dvd_pow_two_mul_sub_one hQ 3) (Nat.eight_dvd_sq_sub_one_of_odd hQ)
    rw [mul_assoc]
    exact Dvd.dvd.mul_left ((by norm_num : (16 : ℕ) ∣ 8 * 8).trans h64) _
  | suzuki k => simp at he
  | reeG2 k => exact absurd rfl (hR k)
  | reeF4 k => simp at he
  | tits => simp at he

theorem orderA_one_ne_orderRee {q : TauCeti.PrimePower} (hq : q.p = 3) (m : ℕ) :
    orderA 1 q.card ≠ orderRee (3 ^ (2 * m + 1)) := by
  obtain ⟨hQ, -, -⟩ := card_facts_of_char_three hq
  have hQk : q.card = 3 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  have h2 : 2 ∣ q.card ^ 2 - 1 := two_dvd_pow_sub_one hQ 2
  have hgcd : Nat.gcd 2 (q.card - 1) = 2 :=
    Nat.gcd_eq_left (by simpa using two_dvd_pow_sub_one hQ 1)
  have hA : orderA 1 q.card = q.card * ((q.card ^ 2 - 1) / 2) := by
    unfold orderA
    rw [show (1 : ℕ) + 1 = 2 from rfl, show 1 * 2 / 2 = 1 from rfl, Finset.Icc_self,
      Finset.prod_singleton, pow_one, hgcd, Nat.mul_div_assoc _ h2]
  intro h
  rw [hA] at h
  obtain ⟨hR3, hM3⟩ := orderRee_eq_three_pow_mul m
  have hX3 : ¬ 3 ∣ (q.card ^ 2 - 1) / 2 := by
    intro h3
    have h3' : 3 ∣ q.card ^ 2 - 1 := h3.trans (Nat.div_dvd_of_dvd h2)
    have hQ0 : q.card ^ 2 % 3 = 0 := by
      rw [hQk, ← pow_mul]
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by have := q.exponent_pos; omega))
    have hQ1 : 1 ≤ q.card ^ 2 := Nat.one_le_pow _ _ hQ.pos
    omega
  rw [hR3, hQk] at h
  have hk := eq_of_prime_pow_mul_eq Nat.prime_three (by rwa [← hQk]) hM3 h
  have hmod : q.card % 16 = 3 ∨ q.card % 16 = 11 := by
    rw [hQk, hk, show 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 by ring]
    exact three_pow_odd_mod_sixteen _
  have hsq : (q.card ^ 2 - 1) % 16 = 8 := by
    have hQ1 : 1 ≤ q.card ^ 2 := Nat.one_le_pow _ _ hQ.pos
    have : q.card ^ 2 % 16 = 9 := by
      rw [Nat.pow_mod]
      rcases hmod with h' | h' <;> rw [h']
    omega
  have hX : (q.card ^ 2 - 1) / 2 % 8 = 4 := by omega
  have h8 : orderRee (3 ^ (2 * m + 1)) % 8 = 0 := by
    have := orderRee_mod_sixteen m
    omega
  rw [hR3, ← h, ← hQk, Nat.mul_mod, hX] at h8
  rcases hmod with h' | h' <;> omega

theorem lieOrderFormula_ne_orderRee {e : TauCeti.LieTypeIndex} (hv : e.Valid)
    (he : e.characteristic = 3) (hR : ∀ k, e ≠ .reeG2 k) (m : ℕ) :
    lieOrderFormula e ≠ orderRee (3 ^ (2 * m + 1)) := by
  by_cases hA : ∃ q, e = .A 1 q
  · obtain ⟨q, rfl⟩ := hA
    exact orderA_one_ne_orderRee (by simpa using he) m
  · push Not at hA
    intro h
    have h16 := sixteen_dvd_lieOrderFormula hv he hA hR
    have := orderRee_mod_sixteen m
    omega

theorem card_of_catalogIs_ree (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (h : catalogIs T (onLie fun d => ∃ m, d = .reeG2 m)) :
    ∃ m, 1 ≤ m ∧ Nat.card T = orderRee (3 ^ (2 * m + 1)) := by
  obtain ⟨i, hi, ⟨φ⟩⟩ := h
  cases i with
  | lie e =>
    obtain ⟨d, hv⟩ := e
    obtain ⟨m, rfl⟩ : ∃ m, d = .reeG2 m := hi
    have hs : 1 ≤ m := by
      simpa using (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    exact ⟨m, hs, hb ⟨_, hv⟩ T ⟨φ⟩⟩
  | _ => exact hi.elim

theorem isEmpty_mulEquiv_lie_of_card_ree (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    {m : ℕ} (hm : 1 ≤ m) (hT : Nat.card T = orderRee (3 ^ (2 * m + 1)))
    (e : TauCeti.ValidLieTypeIndex) (he : ∀ k, e.1 ≠ .reeG2 k) :
    IsEmpty (T ≃* (TauCeti.CFSGIndex.lie e).Group) := by
  refine ⟨fun φ => ?_⟩
  by_cases h3 : e.1.characteristic = 3
  · exact lieOrderFormula_ne_orderRee e.2 h3 he m ((hb e T ⟨φ⟩).symm.trans hT)
  · exact not_lie_char_of_card_ree hb hm hT (TauCeti.LieTypeIndex.characteristic_prime e.1) h3
      ⟨.lie e, rfl, ⟨φ⟩⟩

theorem isEmpty_mulEquiv_alternating_of_card_ree {T : Type} [Group T] [Finite T] {m : ℕ}
    (hm : 1 ≤ m) (hT : Nat.card T = orderRee (3 ^ (2 * m + 1))) (n : ℕ) (hn : 5 ≤ n) :
    IsEmpty (T ≃* alternatingGroup (Fin n)) := by
  refine ⟨fun φ => ?_⟩
  have hc : Nat.card T = n.factorial / 2 :=
    (Nat.card_congr φ.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
  rw [hT] at hc
  have h16 := orderRee_mod_sixteen m
  have hbig := orderRee_ge hm
  generalize orderRee (3 ^ (2 * m + 1)) = N at hc h16 hbig
  by_cases h8 : 8 ≤ n
  · have hf : 2 * 64 ∣ n.factorial :=
      (by decide : 2 * 64 ∣ Nat.factorial 8).trans (Nat.factorial_dvd_factorial h8)
    have h64 : 64 ∣ n.factorial / 2 := Nat.dvd_div_of_mul_dvd hf
    rw [← hc] at h64
    omega
  · interval_cases n <;> simp [Nat.factorial] at hc <;> omega

theorem not_isChevSimple_of_card_ree (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    {m r : ℕ} (hm : 1 ≤ m) (hT : Nat.card T = orderRee (3 ^ (2 * m + 1))) (hr : r.Prime)
    (hr3 : r ≠ 3) : ¬ IsChevSimple r T := by
  rintro (h | ⟨i, hi, ⟨φ⟩⟩)
  · exact not_lie_char_of_card_ree hb hm hT hr hr3 h
  · cases i with
    | alternating n hn => exact (isEmpty_mulEquiv_alternating_of_card_ree hm hT n hn).false φ
    | lie e =>
      refine (isEmpty_mulEquiv_lie_of_card_ree hb hm hT e ?_).false φ
      intro k hk
      obtain ⟨d, hv⟩ := e
      simp only at hk
      subst hk
      simp [ambiguousChev] at hi
    | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.S2019
