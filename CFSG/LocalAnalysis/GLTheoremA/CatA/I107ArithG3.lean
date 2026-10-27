module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithG2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem fam_C {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .C) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  obtain ⟨hn, hr, hr2⟩ := inLambda2_BC hlab (Or.inr ht)
  have hU := upA_of_plain (p := p) (lab := lab) (by rw [ht]; simp)
  rw [hU] at hA
  have hG : twoRankLow107 lab = lab.n * (lab.rank * (lab.rank + 1) / 2) := by
    simp only [twoRankLow107, ht]
  obtain ⟨hE1, hE3⟩ := e_facts hp hp2 hn
  rcases m0_cases (n := lab.n) hp hp2 with ⟨h1, hd1⟩ | ⟨h2, hd2⟩ | h3
  · rw [h1, rk2Mult_BC_one (Or.inr ht)] at hA
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
    rw [hU, hG, h1, rk2Mult_BC_one (Or.inr ht)] at hg'
    generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1 hE3
    exact (arithC_m1 lab.rank lab.n e hE1 hn2 hA hg').elim
  · rw [h2, rk2Mult_BC_two (Or.inr ht)] at hA
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl3 : lab.rank = 3 := by
        simp [ht] at hsurv
        exact hsurv
      refine ⟨eq_three_of_dvd_two_pow_add_one hp (Or.inl hn1) hd2, ?_⟩
      exact Or.inl ⟨hn1, Or.inl ⟨Or.inr ht, hl3⟩⟩
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      rw [hU, hG, h2, rk2Mult_BC_two (Or.inr ht)] at hg'
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1 hE3
      exact (arithC_m2 lab.rank lab.n e hn hE1 hE3 hr2 hA hg').elim
  · have hr3 := rk2Mult_bcd_le (lab := lab) (Or.inr (Or.inl ht)) (m := rk2Ord p lab.n) h3
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
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1
      exact (arithC_m3 lab.rank lab.n e _ hn hE1 hr3 hA hg').elim

theorem fam_twD {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .twD) (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  obtain ⟨hn, hr⟩ := inLambda2_twD hlab ht
  have hU := upA_of_plain (p := p) (lab := lab) (by rw [ht]; simp)
  rw [hU] at hA
  have hG : twoRankLow107 lab = max (lab.n * (2 * lab.rank - 2)) (lab.n * ((lab.rank - 1) * (lab.rank - 2) / 2)) := by
    simp only [twoRankLow107, ht]
  obtain ⟨hE1, hE3⟩ := e_facts hp hp2 hn
  rcases m0_cases (n := lab.n) hp hp2 with ⟨h1, hd1⟩ | ⟨h2, hd2⟩ | h3
  · rw [h1, rk2Mult_twD_one ht] at hA
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
    rw [hU, hG, h1, rk2Mult_twD_one ht] at hg'
    have hgT : lab.n * (2 * lab.rank - 2) ≤ lab.rank - 1 + (if p ∣ lab.n then 1 else 0) + 2 :=
      le_trans (le_max_left _ _) hg'
    generalize (if p ∣ lab.n then 1 else 0) = e at hA hgT hE1
    exact (arithTD_m1 lab.rank lab.n e hE1 hn2 hA hgT).elim
  · rw [h2, rk2Mult_twD_two ht] at hA
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl3 : lab.rank = 3 := by
        simp [ht] at hsurv
        exact hsurv
      refine ⟨eq_three_of_dvd_two_pow_add_one hp (Or.inl hn1) hd2, ?_⟩
      exact Or.inl ⟨hn1, Or.inr (Or.inr (Or.inl ⟨ht, hl3⟩))⟩
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      rw [hU, hG, h2, rk2Mult_twD_two ht] at hg'
      have hgT : lab.n * (2 * lab.rank - 2) ≤ (if lab.rank % 2 = 0 then lab.rank - 1 else lab.rank) +
          (if p ∣ lab.n then 1 else 0) + 2 := le_trans (le_max_left _ _) hg'
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hgT hE1 hE3
      generalize hR : (if lab.rank % 2 = 0 then lab.rank - 1 else lab.rank) = r at hA hgT
      have hrr : (lab.rank % 2 = 0 → r + 1 = lab.rank) ∧ (lab.rank % 2 = 1 → r = lab.rank) := by
        constructor <;> intro h <;> split_ifs at hR <;> omega
      obtain ⟨h1n, hl⟩ := arithTD_m2 lab.rank lab.n e r hn hE1 hE3 (by omega) hrr hA hgT
      have hp3 := eq_three_of_dvd_two_pow_add_one hp (Or.inl h1n) hd2
      exact ⟨hp3, Or.inl ⟨h1n, Or.inr (Or.inr (Or.inl ⟨ht, hl⟩))⟩⟩
  · have hr3 := rk2Mult_bcd_le (lab := lab) (Or.inr (Or.inr (Or.inr ht))) (m := rk2Ord p lab.n) h3
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
      have hgT : lab.n * (2 * lab.rank - 2) ≤ rk2Mult lab (rk2Ord p lab.n) + (if p ∣ lab.n then 1 else 0) + 2 :=
        le_trans (le_max_left _ _) hg'
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hgT hE1
      exact (arithTD_m3 lab.rank lab.n e _ hn hE1 hr3 (by omega) hA hgT).elim

theorem fam_D {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  obtain ⟨hn, hℓ⟩ := inLambda2_D hlab ht
  have hG : twoRankLow107 lab = lab.n * (lab.rank * (lab.rank - 1) / 2) := by
    simp only [twoRankLow107, ht]
  unfold upA107 at hA
  obtain ⟨hE1, hE3⟩ := e_facts hp hp2 hn
  have hbE : (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  have hb4 : (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) = 1 →
      lab.rank = 4 := by
    intro h
    by_cases hc : p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4)
    · rcases hc.2 with ⟨_, h4⟩ | h'
      · exact h4
      · simp [ht] at h'
    · rw [if_neg hc] at h
      omega
  rcases m0_cases (n := lab.n) hp hp2 with ⟨h1, hd1⟩ | ⟨h2, hd2⟩ | h3
  · rw [h1, rk2Mult_D_one ht] at hA
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
    unfold upA107 at hg'
    rw [hG, h1, rk2Mult_D_one ht] at hg'
    generalize (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) = b at hA hg' hbE hb4
    generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1 hE3
    exact (arithD_m1 lab.rank lab.n e b hE1 hbE hb4 hn2 hE3 hℓ hA hg').elim
  · rw [h2, rk2Mult_D_two ht] at hA
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl4 : lab.rank = 4 := by
        simp [ht] at hsurv
        exact hsurv
      refine ⟨eq_three_of_dvd_two_pow_add_one hp (Or.inl hn1) hd2, ?_⟩
      exact Or.inl ⟨hn1, Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hl4⟩)))⟩
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      unfold upA107 at hg'
      rw [hG, h2, rk2Mult_D_two ht] at hg'
      generalize hR : (if lab.rank % 2 = 0 then lab.rank else lab.rank - 1) = r at hA hg'
      have hrr : (lab.rank % 2 = 0 → r = lab.rank) ∧ (lab.rank % 2 = 1 → r + 1 = lab.rank) := by
        constructor <;> intro h <;> split_ifs at hR <;> omega
      generalize (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) = b at hA hg' hbE hb4
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1 hE3
      obtain ⟨h1n, hl⟩ := arithD_m2 lab.rank lab.n e b r hn hE1 hbE hb4 hE3 hℓ hrr hA hg'
      have hp3 := eq_three_of_dvd_two_pow_add_one hp (Or.inl h1n) hd2
      exact ⟨hp3, Or.inl ⟨h1n, Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hl⟩)))⟩⟩
  · have hr3 := rk2Mult_bcd_le (lab := lab) (Or.inr (Or.inr (Or.inl ht))) (m := rk2Ord p lab.n) h3
    rw [bonus_zero_of_m0 h3] at hA
    by_cases hex : exempt107 lab
    · obtain ⟨hn1, hsurv⟩ := hex
      have hl4 : lab.rank = 4 := by simp [ht] at hsurv; exact hsurv
      have he0 : (if p ∣ lab.n then 1 else 0) = 0 := by
        rw [if_neg]; rw [hn1]; intro hd; exact hp.ne_one (Nat.dvd_one.1 hd)
      rw [he0] at hA
      rw [hl4] at hr3
      omega
    · have hg' : twoRankLow107 lab ≤ upA107 lab p + 2 := hg.resolve_left hex
      unfold upA107 at hg'
      rw [hG] at hg'
      rw [bonus_zero_of_m0 h3] at hg'
      generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' hE1 hE3
      exact (arithD_m3 lab.rank lab.n e _ hn hE1 hr3 hℓ hA hg').elim

end CFSG.LocalAnalysis.GLTheoremA

end
