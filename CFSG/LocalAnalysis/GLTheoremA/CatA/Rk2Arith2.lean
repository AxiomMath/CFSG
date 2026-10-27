module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

section Tags2

variable {p : ℕ} {c : Prop} {e : ℕ}

theorem rk2_half_BC {lab : GLALabel} (ht : lab.tag = .B ∨ lab.tag = .C) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p (rk2Norm lab) c := by
  have htB : (rk2Norm lab).tag = .B := by
    rcases ht with ht | ht
    · rw [rk2Norm_of_ne (by rw [ht]; decide)]; exact ht
    · exact rk2Norm_tag_of_C ht
  have hmpos := rk2Ord_pos hp hp2 lab.n
  by_cases hm1 : rk2Ord p lab.n = 1
  · refine rk2_half_of_split (rk2_split_untw ?_ ?_)
    · rw [htB]; trivial
    · simpa using rk2Ord_eq_one_iff.1 hm1
  by_cases hm2 : rk2Ord p lab.n = 2
  · refine rk2_half_b (Or.inl htB) ?_
    simpa using (rk2Ord_eq_two_iff hp hp2).1 hm2
  exfalso
  have hm3 : 3 ≤ rk2Ord p lab.n := by omega
  have hle := rk2Mult_bcd_le (lab := lab) (by tauto) hm3
  have hbcd : lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D := by tauto
  by_cases hn1 : lab.n = 1
  · have := hE.bcd_one hbcd hn1
    omega
  · have := hE.bcd_ge hbcd (by omega)
    omega

theorem rk2_half_D {lab : GLALabel} (ht : lab.tag = .D) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p lab c := by
  have hmpos := rk2Ord_pos hp hp2 lab.n
  by_cases hm1 : rk2Ord p lab.n = 1
  · refine rk2_half_of_split (rk2_split_untw ?_ ?_)
    · rw [ht]; trivial
    · simpa using rk2Ord_eq_one_iff.1 hm1
  by_cases hm2 : rk2Ord p lab.n = 2
  · refine rk2_half_b (Or.inr (Or.inl ht)) ?_
    simpa using (rk2Ord_eq_two_iff hp hp2).1 hm2
  exfalso
  have hm3 : 3 ≤ rk2Ord p lab.n := by omega
  have hle := rk2Mult_bcd_le (lab := lab) (by tauto) hm3
  have hbcd : lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D := by tauto
  by_cases hn1 : lab.n = 1
  · have := hE.bcd_one hbcd hn1
    omega
  · have := hE.bcd_ge hbcd (by omega)
    omega

theorem rk2_half_twD {lab : GLALabel} (ht : lab.tag = .twD) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p lab c := by
  have hmpos := rk2Ord_pos hp hp2 lab.n
  by_cases hm1 : rk2Ord p lab.n = 1
  · exact rk2_half_of_split (rk2_split_c (Or.inl ht) (rk2Ord_eq_one_iff.1 hm1))
  by_cases hm2 : rk2Ord p lab.n = 2
  · refine rk2_half_of_split (rk2_split_tw ?_ ?_ ?_ ((rk2Ord_eq_two_iff hp hp2).1 hm2))
    · rw [ht]; simp [CFSG.Assembly.LargeEvenUntwisted]
    · rw [ht]; decide
    · rw [ht]; decide
  exfalso
  have hm3 : 3 ≤ rk2Ord p lab.n := by omega
  have hle := rk2Mult_bcd_le (lab := lab) (by tauto) hm3
  have := hE.twd ht
  omega

private theorem not_dvd_seven_or_eight {n : ℕ} (hn : 1 ≤ n) (a : ℕ) (ha : a = 7 ∨ a = 8) : ¬ 2 ^ n + 1 ∣ a := by
  intro h
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases ha with rfl | rfl
  · have hle := Nat.le_of_dvd (by norm_num) h
    have h7 : 2 ^ n + 1 = 7 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 h with h1 | h1
      · omega
      · exact h1
    have h6 : 2 ^ n = 6 := by omega
    have h3 : 3 ∣ 2 ^ n := ⟨2, by omega⟩
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · have hodd : Nat.Coprime (2 ^ n + 1) 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    have hc : Nat.Coprime (2 ^ n + 1) 8 := by
      have := Nat.Coprime.pow_right 3 hodd
      simpa using this
    have := Nat.Coprime.eq_one_of_dvd hc h
    omega

theorem rk2_half_twA {lab : GLALabel} (ht : lab.tag = .twA) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p lab c := by
  have hmpos := rk2Ord_pos hp hp2 lab.n
  by_cases hm2 : rk2Ord p lab.n = 2
  · refine rk2_half_of_split (rk2_split_tw ?_ ?_ ?_ ((rk2Ord_eq_two_iff hp hp2).1 hm2))
    · rw [ht]; simp [CFSG.Assembly.LargeEvenUntwisted]
    · rw [ht]; decide
    · rw [ht]; decide
  by_cases hm1 : rk2Ord p lab.n = 1
  · have hmult : rk2Mult lab (rk2Ord p lab.n) = (lab.rank + 1) / 2 := by
      simp [rk2Mult, ht, hm1]
    rw [hmult] at hr he
    by_cases hℓ5 : lab.rank = 5
    · exact rk2_half_c (Or.inl ⟨ht, hℓ5⟩) (rk2Ord_eq_one_iff.1 hm1)
    exfalso
    have hℓ : 6 ≤ lab.rank := by omega
    by_cases hℓ8 : 8 ≤ lab.rank
    · have := hE.twa_two ht
      omega
    · have hdiv : ¬ 2 ^ lab.n + 1 ∣ lab.rank + 1 :=
        not_dvd_seven_or_eight hn _ (by omega)
      have := hE.twa_one ht hdiv
      omega
  exfalso
  have hm3 : 3 ≤ rk2Ord p lab.n := by omega
  have hle := rk2Mult_twA_le ht hm3
  have := hE.twa_two ht
  omega

theorem rk2_half_E6 {lab : GLALabel} (ht : lab.tag = .E6) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p lab c := by
  have hmpos := rk2Ord_pos hp hp2 lab.n
  have hmult : ∀ m, rk2Mult lab m =
      rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] m := by
    intro m; simp [rk2Mult, ht]
  rw [hmult] at hr he
  rcases rk2_E6_ge3 hr with hm | hm | hm
  · exact rk2_half_of_split (rk2_split_untw (by rw [ht]; trivial) (rk2Ord_eq_one_iff.1 hm))
  · have hr4 : rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)]
        (rk2Ord p lab.n) = 4 := by rw [hm]; decide
    rw [hr4] at he
    by_cases hn1 : lab.n = 1
    · have hp3 : p = 3 := by
        have := hm
        rw [hn1] at this
        exact (rk2Ord_one_eq_two_iff hp hp2).1 this
      exact rk2_half_of_split (rk2_split_n1 hn1 hp3)
    · have hn2 : 2 ≤ lab.n := by omega
      by_cases hcn : lab.n = 2 ∧ c
      · have hp5 : p = 5 := by
          have h1 := (rk2Ord_eq_two_iff hp hp2).1 hm
          rw [hcn.1] at h1
          exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using h1)
        exact rk2_half_d (Or.inr ht) hcn.1 hcn.2 hp5
      · exfalso
        have := hE.e6_big ht (by
          by_cases h3 : 3 ≤ lab.n
          · exact Or.inl h3
          · exact Or.inr ⟨by omega, fun hc => hcn ⟨by omega, hc⟩⟩)
        omega
  · have hr3 : rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)]
        (rk2Ord p lab.n) = 3 := by rw [hm]; decide
    rw [hr3] at he
    by_cases hn1 : lab.n = 1
    · have hp7 : p = 7 := by
        have := hm
        rw [hn1] at this
        exact (rk2Ord_one_eq_three_iff hp).1 this
      exact rk2_half_e2 ht hn1 hp7
    · exfalso
      have := hE.e6_two ht (by omega)
      omega

theorem rk2_half_E7 {lab : GLALabel} (ht : lab.tag = .E7) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p lab c := by
  have hmpos := rk2Ord_pos hp hp2 lab.n
  have hmult : ∀ m, rk2Mult lab m =
      rk2Cnt [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)] m := by
    intro m; simp [rk2Mult, ht]
  rw [hmult] at hr he
  rcases rk2_E7_ge3 hr with hm | hm | hm | hm
  · exact rk2_half_of_split (rk2_split_untw (by rw [ht]; trivial) (rk2Ord_eq_one_iff.1 hm))
  · exact rk2_half_b (Or.inr (Or.inr (Or.inr (Or.inl ht)))) (by simpa using (rk2Ord_eq_two_iff hp hp2).1 hm)
  all_goals
    exfalso
    have hr3 : rk2Cnt [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)]
        (rk2Ord p lab.n) = 3 := by rw [hm]; decide
    rw [hr3] at he
    by_cases hn1 : lab.n = 1
    · have := hE.e7_one ht hn1
      omega
    · have := hE.e7 ht (by omega)
      omega

theorem rk2_half_E8 {lab : GLALabel} (ht : lab.tag = .E8) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p lab c := by
  have hmpos := rk2Ord_pos hp hp2 lab.n
  have hmult : ∀ m, rk2Mult lab m =
      rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true), (30, true)] m := by
    intro m; simp [rk2Mult, ht]
  rw [hmult] at hr he
  rcases rk2_E8_ge3 hr with hm | hm | hm | hm | hm
  · exact rk2_half_of_split (rk2_split_untw (by rw [ht]; trivial) (rk2Ord_eq_one_iff.1 hm))
  · exact rk2_half_b (Or.inr (Or.inr (Or.inr (Or.inr ht)))) (by simpa using (rk2Ord_eq_two_iff hp hp2).1 hm)
  all_goals
    exfalso
    have hr4 : rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true), (30, true)]
        (rk2Ord p lab.n) = 4 := by rw [hm]; decide
    rw [hr4] at he
    by_cases hn1 : lab.n = 1
    · have := hE.e8_one ht hn1
      omega
    · have := hE.e8 ht (by omega)
      omega

theorem rk2_half_F4 {lab : GLALabel} (ht : lab.tag = .F4) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) :
    GLAHalfSplit16 p lab c := by
  have hmult : ∀ m, rk2Mult lab m = rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m := by
    intro m; simp [rk2Mult, ht]
  rw [hmult] at hr
  rcases rk2_F4_ge3 hr with hm | hm
  · exact rk2_half_of_split (rk2_split_untw (by rw [ht]; trivial) (rk2Ord_eq_one_iff.1 hm))
  · exact rk2_half_b (Or.inr (Or.inr (Or.inl ht))) (by simpa using (rk2Ord_eq_two_iff hp hp2).1 hm)

theorem rk2_half_twE6 {lab : GLALabel} (ht : lab.tag = .twE6) (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt lab c e)
    (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) :
    GLAHalfSplit16 p lab c := by
  have hmpos := rk2Ord_pos hp hp2 lab.n
  have hmult : ∀ m, rk2Mult lab m =
      rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] m := by
    intro m; simp [rk2Mult, ht]
  rw [hmult] at hr he
  rcases rk2_twE6_ge3 hr with hm | hm | hm
  · exact rk2_half_c (Or.inr ht) (rk2Ord_eq_one_iff.1 hm)
  · refine rk2_half_of_split (rk2_split_tw ?_ ?_ ?_ ((rk2Ord_eq_two_iff hp hp2).1 hm))
    · rw [ht]; simp [CFSG.Assembly.LargeEvenUntwisted]
    · rw [ht]; decide
    · rw [ht]; decide
  · exfalso
    have hr3 : rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)]
        (rk2Ord p lab.n) = 3 := by rw [hm]; decide
    rw [hr3] at he
    by_cases hn1 : lab.n = 1
    ·
      have hdvd : p ∣ 2 ^ (1 * 6) - 1 := by
        have h6 : rk2Ord p 1 ∣ 6 := by rw [← hn1, hm]
        exact (rk2Ord_dvd_iff (p := p) (n := 1) 6).1 (by rw [hn1] at hm; rw [hm])
      have h63 : p ∣ 3 ^ 2 * 7 := by norm_num at hdvd ⊢; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).1 h63 with h | h
      · have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
        have := (rk2Ord_one_eq_two_iff hp hp2).2 h3
        rw [hn1] at hm
        omega
      · have h7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
        have := (rk2Ord_one_eq_three_iff hp).2 h7
        rw [hn1] at hm
        omega
    · have := hE.twe6 ht (by omega)
      omega

theorem rk2Mult_le_two_of_small {lab : GLALabel}
    (ht : lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
      lab.tag = .G2der ∨ lab.tag = .twF4der) {m : ℕ} (hm : 0 < m) : rk2Mult lab m ≤ 2 := by
  rcases ht with ht | ht | ht | ht | ht | ht | ht
  · simp only [rk2Mult, ht]; exact rk2_G2_le
  · simp only [rk2Mult, ht]; exact rk2_triD4_le
  · simp only [rk2Mult, ht]; exact rk2_twB2_le
  · simp only [rk2Mult, ht]; exact rk2_twF4_le
  · simp only [rk2Mult, ht]
    split_ifs with h
    · have h2 : 2 ≤ m := by omega
      calc 4 / m ≤ 4 / 2 := Nat.div_le_div_left h2 (by norm_num)
        _ = 2 := by norm_num
    · exact (Nat.div_le_self 2 m)
  · simp only [rk2Mult, ht]; exact rk2_G2_le
  · simp only [rk2Mult, ht]; exact rk2_twF4_le

end Tags2

theorem rk2_half_of_rank {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c : Prop} {e : ℕ} (hr : 3 ≤ rk2Mult lab (rk2Ord p lab.n)) (hE : Rk2ELowAt lab c e)
    (he : e ≤ rk2Mult lab (rk2Ord p lab.n) + 1) : GLAHalfSplit16 p (rk2Norm lab) c := by
  have hn : 1 ≤ lab.n := hlab.1
  have hmpos := rk2Ord_pos hp hp2 lab.n
  by_cases hC : lab.tag = .C
  · exact rk2_half_BC (Or.inr hC) hn hp hp2 hE hr he
  rw [rk2Norm_of_ne hC]
  obtain ⟨t, ℓ, n⟩ := lab
  cases t
  · exact rk2_half_A hp hp2 hE hr he
  · exact rk2_half_twA rfl hn hp hp2 hE hr he
  · have h := rk2_half_BC (lab := ⟨.B, ℓ, n⟩) (Or.inl rfl) hn hp hp2 hE hr he
    rwa [rk2Norm_of_ne (lab := ⟨.B, ℓ, n⟩)
      (by simp only; exact (by decide : CFSG.Assembly.LargeEvenLieTag.B ≠ CFSG.Assembly.LargeEvenLieTag.C))] at h
  · exact absurd rfl hC
  · exact rk2_half_D rfl hn hp hp2 hE hr he
  · exact rk2_half_twD rfl hn hp hp2 hE hr he
  · exact rk2_half_E6 rfl hn hp hp2 hE hr he
  · exact rk2_half_E7 rfl hn hp hp2 hE hr he
  · exact rk2_half_E8 rfl hn hp hp2 hE hr he
  · exact rk2_half_F4 rfl hn hp hp2 hr
  · exact rk2_half_twE6 rfl hn hp hp2 hE hr he
  · exfalso
    have := rk2Mult_le_two_of_small (lab := ⟨.triD4, ℓ, n⟩) (Or.inr (Or.inl rfl)) hmpos
    omega
  · exfalso
    have := rk2Mult_le_two_of_small (lab := ⟨.G2, ℓ, n⟩) (Or.inl rfl) hmpos
    omega
  · exfalso
    have := rk2Mult_le_two_of_small (lab := ⟨.twB2, ℓ, n⟩) (Or.inr (Or.inr (Or.inl rfl))) hmpos
    omega
  · exfalso
    have := rk2Mult_le_two_of_small (lab := ⟨.twF4, ℓ, n⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hmpos
    omega
  · exfalso
    have := rk2Mult_le_two_of_small (lab := ⟨.B2der, ℓ, n⟩)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hmpos
    omega
  · exfalso
    have := rk2Mult_le_two_of_small (lab := ⟨.G2der, ℓ, n⟩)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hmpos
    omega
  · exfalso
    have := rk2Mult_le_two_of_small (lab := ⟨.twF4der, ℓ, n⟩)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hmpos
    omega

end CFSG.LocalAnalysis.GLTheoremA
