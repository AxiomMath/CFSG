module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithF1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Arith

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem rk2Mult_A {lab : GLALabel} (ht : lab.tag = .A) (m : ℕ) :
    rk2Mult lab m = if m = 1 then lab.rank else (lab.rank + 1) / m := by
  simp [rk2Mult, ht]

theorem rk2Mult_twA_one {lab : GLALabel} (ht : lab.tag = .twA) : rk2Mult lab 1 = (lab.rank + 1) / 2 := by
  simp [rk2Mult, ht]

theorem rk2Mult_twA_two {lab : GLALabel} (ht : lab.tag = .twA) : rk2Mult lab 2 = lab.rank := by
  simp [rk2Mult, ht]

theorem inLambda2_A {lab : GLALabel} (h : GLAInLambda2 lab) (ht : lab.tag = .A) :
    1 ≤ lab.n ∧ 1 ≤ lab.rank ∧ (lab.rank = 1 → 2 ≤ lab.n) := by
  unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at h
  rw [ht] at h
  exact h

theorem inLambda2_twA {lab : GLALabel} (h : GLAInLambda2 lab) (ht : lab.tag = .twA) :
    1 ≤ lab.n ∧ 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
  unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at h
  rw [ht] at h
  exact h

theorem upA_of_tag {lab : GLALabel} {p : ℕ} (ht : lab.tag = .A ∨ lab.tag = .twA) :
    upA107 lab p = rk2Mult lab (rk2Ord p lab.n) + (if p ∣ lab.n then 1 else 0) := by
  unfold upA107
  rcases ht with ht | ht <;> simp [ht]

theorem three_le_of_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ n) (hn : 1 ≤ n) : 3 ≤ n := by
  have h1 := Nat.le_of_dvd (by omega) hd
  have h2 := hp.two_le
  omega

theorem not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro hd
  have h2 : p ∣ 2 ^ 2 := by norm_num; exact hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))

theorem not_dvd_five {p : ℕ} (hp : p.Prime) (hd5 : p ∣ 5) (hd33 : p ∣ 2 ^ 5 + 1) : False := by
  have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hd5
  subst h5
  norm_num at hd33

theorem eq_three_of_dvd_two_pow_add_one {p n : ℕ} (hp : p.Prime) (hn : n = 1 ∨ n = 3) (hd : p ∣ 2 ^ n + 1) :
    p = 3 := by
  rcases hn with rfl | rfl
  · norm_num at hd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd
  · have h3 : p ∣ 3 ^ 2 := by norm_num; exact hd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)

theorem e_three {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) :
    (p ∣ n → 3 ≤ n) := fun hd => three_le_of_dvd hp hp2 hd hn

theorem fam_A {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .A) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) : p = 3 ∧ survivor107 lab := by
  exfalso
  have hex : ¬ exempt107 lab := by
    intro h; unfold exempt107 at h; rw [ht] at h; simp at h
  have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
  obtain ⟨hn, hr, _⟩ := inLambda2_A hlab ht
  have hG : twoRankLow107 lab = lab.n * ((lab.rank + 1) ^ 2 / 4) := by simp only [twoRankLow107, ht]
  have hU := upA_of_tag (p := p) (Or.inl ht)
  rw [hU] at hA hg'
  rw [hG] at hg'
  have he3 := e_three hp hp2 hn
  rcases m0_cases (n := lab.n) hp hp2 with ⟨h1, hd1⟩ | ⟨h2, hd2⟩ | h3
  · rw [h1, rk2Mult_A ht] at hA hg'
    simp only [if_true] at hA hg'
    have hn2 : 2 ≤ lab.n := by
      by_contra hc
      have h1n : lab.n = 1 := by omega
      rw [h1n] at hd1
      norm_num at hd1
      exact hp.ne_one hd1
    by_cases hpn : p ∣ lab.n
    · simp only [hpn, if_true] at hA hg'
      exact arithA_m1 lab.rank lab.n 1 le_rfl hn2 (fun _ => he3 hpn) hA hg'
    · simp only [hpn, if_false] at hA hg'
      exact arithA_m1 lab.rank lab.n 0 (by norm_num) hn2 (fun h => absurd h (by norm_num)) hA hg'
  · rw [h2, rk2Mult_A ht] at hA hg'
    simp only [show (2 : ℕ) ≠ 1 by norm_num, if_false] at hA hg'
    by_cases hpn : p ∣ lab.n
    · simp only [hpn, if_true] at hA hg'
      exact arithA_m2 lab.rank lab.n 1 hn le_rfl (fun _ => he3 hpn) hA hg'
    · simp only [hpn, if_false] at hA hg'
      exact arithA_m2 lab.rank lab.n 0 hn (by norm_num) (fun h => absurd h (by norm_num)) hA hg'
  · rw [rk2Mult_A ht] at hA hg'
    have hm1 : rk2Ord p lab.n ≠ 1 := by omega
    simp only [hm1, if_false] at hA hg'
    have hdiv : (lab.rank + 1) / rk2Ord p lab.n ≤ (lab.rank + 1) / 3 :=
      Nat.div_le_div_left h3 (by norm_num)
    by_cases hpn : p ∣ lab.n
    · simp only [hpn, if_true] at hA hg'
      exact arithA_m3 lab.rank lab.n 1 _ hn le_rfl hdiv hA hg'
    · simp only [hpn, if_false] at hA hg'
      exact arithA_m3 lab.rank lab.n 0 _ hn (by norm_num) hdiv hA hg'


theorem e_facts {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) :
    (if p ∣ n then 1 else 0) ≤ 1 ∧ ((if p ∣ n then 1 else 0) = 1 → 3 ≤ n) := by
  constructor
  · split_ifs <;> omega
  · intro h
    by_cases hd : p ∣ n
    · exact three_le_of_dvd hp hp2 hd hn
    · rw [if_neg hd] at h; omega

theorem fam_twA {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .twA) (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  obtain ⟨hn, hr, hr2⟩ := inLambda2_twA hlab ht
  have hG : twoRankLow107 lab = lab.n * ((lab.rank + 1) / 2) ^ 2 := by simp only [twoRankLow107, ht]
  have hU := upA_of_tag (p := p) (Or.inr ht)
  rw [hU] at hA
  obtain ⟨hE1, hE3⟩ := e_facts hp hp2 hn
  rcases m0_cases (n := lab.n) hp hp2 with ⟨h1, hd1⟩ | ⟨h2, hd2⟩ | h3
  ·
    rw [h1, rk2Mult_twA_one ht] at hA
    have hn2 : 2 ≤ lab.n := by
      by_contra hc
      have h1n : lab.n = 1 := by omega
      rw [h1n] at hd1
      norm_num at hd1
      exact hp.ne_one hd1
    have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := by
      rcases hg with hex | hg
      · have := hex.1; omega
      · exact hg
    rw [hU, hG, h1, rk2Mult_twA_one ht] at hg'
    generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1 hE3
    exact (arithT_m1 lab.rank lab.n e hE1 hn2 hE3 hA hg').elim
  ·
    rw [h2, rk2Mult_twA_two ht] at hA
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl3 : lab.rank = 3 := by simpa [ht] using hsurv
      refine ⟨eq_three_of_dvd_two_pow_add_one hp (Or.inl hn1) hd2, ?_⟩
      exact Or.inl ⟨hn1, Or.inr (Or.inl ⟨ht, Or.inl hl3⟩)⟩
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      rw [hU, hG, h2, rk2Mult_twA_two ht] at hg'
      have hE45 : (if p ∣ lab.n then 1 else 0) = 1 → 3 ≤ lab.n ∧ lab.n ≠ 4 ∧ lab.n ≠ 5 := by
        intro h
        have hd : p ∣ lab.n := by
          by_contra hc
          rw [if_neg hc] at h
          omega
        refine ⟨hE3 h, ?_, ?_⟩
        · intro h4
          rw [h4] at hd
          exact not_dvd_four hp hp2 hd
        · intro h5
          rw [h5] at hd hd2
          exact not_dvd_five hp hd hd2
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1 hE45
      rcases arithT_m2 lab.rank lab.n e hn hE1 hE45 hr hr2 hA hg' with ⟨h1n, hl⟩ | ⟨hl, hn3, he1⟩
      · have hp3 := eq_three_of_dvd_two_pow_add_one hp (Or.inl h1n) hd2
        refine ⟨hp3, Or.inl ⟨h1n, Or.inr (Or.inl ⟨ht, ?_⟩)⟩⟩
        omega
      · have hp3 := eq_three_of_dvd_two_pow_add_one hp (Or.inr hn3) hd2
        exact ⟨hp3, Or.inr ⟨ht, hl, hn3⟩⟩
  ·
    have hr3 := rk2Mult_twA_le ht h3 (m := rk2Ord p lab.n)
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl3 : lab.rank = 3 := by simpa [ht] using hsurv
      have he0 : (if p ∣ lab.n then 1 else 0) = 0 := by
        rw [if_neg]; rw [hn1]; intro hd; exact hp.ne_one (Nat.dvd_one.1 hd)
      rw [he0] at hA
      rw [hl3] at hr3
      omega
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      rw [hU, hG] at hg'
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1
      exact (arithT_m3 lab.rank lab.n e _ hn hE1 hr3 hA hg').elim

end CFSG.LocalAnalysis.GLTheoremA

end
