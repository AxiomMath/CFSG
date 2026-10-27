module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithG1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithF2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem inLambda2_BC {lab : GLALabel} (h : GLAInLambda2 lab) (ht : lab.tag = .B ∨ lab.tag = .C) :
    1 ≤ lab.n ∧ 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
  unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at h
  rcases ht with ht | ht <;> rw [ht] at h <;> exact h

theorem inLambda2_D {lab : GLALabel} (h : GLAInLambda2 lab) (ht : lab.tag = .D) :
    1 ≤ lab.n ∧ 3 ≤ lab.rank := by
  unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at h
  rw [ht] at h
  exact h

theorem inLambda2_twD {lab : GLALabel} (h : GLAInLambda2 lab) (ht : lab.tag = .twD) :
    1 ≤ lab.n ∧ 2 ≤ lab.rank := by
  unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at h
  rw [ht] at h
  exact h

theorem upA_of_plain {lab : GLALabel} {p : ℕ} (h : ¬ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4)) :
    upA107 lab p = rk2Mult lab (rk2Ord p lab.n) + (if p ∣ lab.n then 1 else 0) := by
  unfold upA107
  have hb : ¬ (p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4)) := fun h' => h h'.2
  rw [if_neg hb, add_zero]

theorem rk2Ord_three_dvd_two (n : ℕ) : rk2Ord 3 n ∣ 2 := by
  unfold rk2Ord
  apply orderOf_dvd_of_pow_eq_one
  rw [← pow_mul, mul_comm, pow_mul]
  have h9 : (2 : ZMod 3) ^ 2 = 1 := by decide
  rw [h9, one_pow]

theorem rk2Ord_three_le (n : ℕ) : rk2Ord 3 n ≤ 2 :=
  Nat.le_of_dvd (by norm_num) (rk2Ord_three_dvd_two n)

theorem bonus_zero_of_m0 {lab : GLALabel} {p : ℕ} (h3 : 3 ≤ rk2Ord p lab.n) :
    (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) = 0 := by
  rw [if_neg]
  rintro ⟨hp3, -⟩
  subst hp3
  have := rk2Ord_three_le lab.n
  omega

theorem rk2Mult_BC_one {lab : GLALabel} (ht : lab.tag = .B ∨ lab.tag = .C) : rk2Mult lab 1 = lab.rank := by
  rcases ht with ht | ht <;> simp [rk2Mult, ht]

theorem rk2Mult_BC_two {lab : GLALabel} (ht : lab.tag = .B ∨ lab.tag = .C) : rk2Mult lab 2 = lab.rank := by
  rcases ht with ht | ht <;> simp [rk2Mult, ht] <;> omega

theorem rk2Mult_D_one {lab : GLALabel} (ht : lab.tag = .D) : rk2Mult lab 1 = lab.rank := by
  simp [rk2Mult, ht]

theorem rk2Mult_D_two {lab : GLALabel} (ht : lab.tag = .D) :
    rk2Mult lab 2 = if lab.rank % 2 = 0 then lab.rank else lab.rank - 1 := by
  unfold rk2Mult
  simp only [ht]
  split_ifs <;> omega

theorem rk2Mult_twD_one {lab : GLALabel} (ht : lab.tag = .twD) : rk2Mult lab 1 = lab.rank - 1 := by
  simp [rk2Mult, ht]

theorem rk2Mult_twD_two {lab : GLALabel} (ht : lab.tag = .twD) :
    rk2Mult lab 2 = if lab.rank % 2 = 0 then lab.rank - 1 else lab.rank := by
  unfold rk2Mult
  simp only [ht]
  split_ifs <;> omega

theorem arithC_m2 (ℓ n e : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (he3 : e = 1 → 3 ≤ n) (hl2 : ℓ = 2 → 2 ≤ n)
    (hA : 3 ≤ ℓ + e) (hg : n * (ℓ * (ℓ + 1) / 2) ≤ ℓ + e + 2) : False := by
  have h1 : ℓ * (ℓ + 1) / 2 ≤ n * (ℓ * (ℓ + 1) / 2) := Nat.le_mul_of_pos_left _ hn
  have hl : ℓ ≤ 4 := by
    by_contra hc
    have h2 : 2 * ℓ ≤ ℓ * (ℓ + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith
    omega
  interval_cases ℓ <;> interval_cases e <;> (try norm_num at he3 hl2 hg hA) <;> omega

theorem fam_B {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .B) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  obtain ⟨hn, hr, hr2⟩ := inLambda2_BC hlab (Or.inl ht)
  have hU := upA_of_plain (p := p) (lab := lab) (by rw [ht]; simp)
  rw [hU] at hA
  have hG : twoRankLow107 lab = max (lab.n * (2 * lab.rank - 1)) (lab.n * (lab.rank * (lab.rank - 1) / 2)) := by
    simp only [twoRankLow107, ht]
  obtain ⟨hE1, hE3⟩ := e_facts hp hp2 hn
  rcases m0_cases (n := lab.n) hp hp2 with ⟨h1, hd1⟩ | ⟨h2, hd2⟩ | h3
  · rw [h1, rk2Mult_BC_one (Or.inl ht)] at hA
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
    rw [hU, hG, h1, rk2Mult_BC_one (Or.inl ht)] at hg'
    have hgB : lab.n * (2 * lab.rank - 1) ≤ lab.rank + (if p ∣ lab.n then 1 else 0) + 2 :=
      le_trans (le_max_left _ _) hg'
    generalize (if p ∣ lab.n then 1 else 0) = e at hA hgB hE1 hE3
    exact (arithB_m1 lab.rank lab.n e hE1 hn2 hA hgB).elim
  · rw [h2, rk2Mult_BC_two (Or.inl ht)] at hA
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl3 : lab.rank = 3 := by
        simp [ht] at hsurv
        exact hsurv
      refine ⟨eq_three_of_dvd_two_pow_add_one hp (Or.inl hn1) hd2, ?_⟩
      exact Or.inl ⟨hn1, Or.inl ⟨Or.inl ht, hl3⟩⟩
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      rw [hU, hG, h2, rk2Mult_BC_two (Or.inl ht)] at hg'
      have hgB : lab.n * (2 * lab.rank - 1) ≤ lab.rank + (if p ∣ lab.n then 1 else 0) + 2 :=
        le_trans (le_max_left _ _) hg'
      have hE23 : (if p ∣ lab.n then 1 else 0) = 1 → 3 ≤ lab.n := hE3
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hgB hE1 hE23
      obtain ⟨h1n, hl⟩ := arithB_m2 lab.rank lab.n e hn hE1 hE23 hr2 hA hgB
      have hp3 := eq_three_of_dvd_two_pow_add_one hp (Or.inl h1n) hd2
      exact ⟨hp3, Or.inl ⟨h1n, Or.inl ⟨Or.inl ht, hl⟩⟩⟩
  · have hr3 := rk2Mult_bcd_le (lab := lab) (Or.inl ht) (m := rk2Ord p lab.n) h3
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl3 : lab.rank = 3 := by simp [ht] at hsurv; exact hsurv
      have he0 : (if p ∣ lab.n then 1 else 0) = 0 := by
        rw [if_neg]; rw [hn1]; intro hd; exact hp.ne_one (Nat.dvd_one.1 hd)
      rw [he0] at hA
      rw [hl3] at hr3
      omega
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      rw [hU, hG] at hg'
      have hgB : lab.n * (2 * lab.rank - 1) ≤ rk2Mult lab (rk2Ord p lab.n) + (if p ∣ lab.n then 1 else 0) + 2 :=
        le_trans (le_max_left _ _) hg'
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hgB hE1
      exact (arithB_m3 lab.rank lab.n e _ hn hE1 hr3 hA hgB).elim

end CFSG.LocalAnalysis.GLTheoremA

end
