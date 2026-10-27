module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithF3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ArithG2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem kill_rank0 {lab : GLALabel} {p : ℕ} (hp : p.Prime) (hn : 1 ≤ lab.n) {c R : ℕ} (hR : R + 2 < c)
    (hr : rk2Mult lab (rk2Ord p lab.n) ≤ R) (hg : c * lab.n ≤ rk2Mult lab (rk2Ord p lab.n) + (if p ∣ lab.n then 1 else 0) + 2) :
    False := by
  have he1 : (if p ∣ lab.n then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hn1 : lab.n = 1 → (if p ∣ lab.n then 1 else 0) = 0 := by
    intro h1
    rw [if_neg]
    rw [h1]
    intro hd
    exact hp.ne_one (Nat.dvd_one.1 hd)
  exact arith0_kill c R lab.n _ _ hn he1 hn1 hr hR hg

theorem fam_E {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p)
    (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) : p = 3 ∧ survivor107 lab := by
  exfalso
  have hn : 1 ≤ lab.n := by
    unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at hlab
    rcases ht with h | h | h <;> rw [h] at hlab <;> exact hlab.1
  have hex : ¬ exempt107 lab := by
    intro h; unfold exempt107 at h; rcases ht with h' | h' | h' <;> simp [h'] at h
  have hg' := hg.resolve_left hex
  have hU := upA_of_plain (p := p) (lab := lab) (by rcases ht with h | h | h <;> simp [h])
  have hG : twoRankLow107 lab = 16 * lab.n := by
    rcases ht with h | h | h <;> simp only [twoRankLow107, h]
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 8 := by
    unfold rk2Mult
    rcases ht with h | h | h <;> simp only [h] <;> unfold rk2Cnt <;>
      exact le_trans List.countP_le_length (by simp)
  rw [hU, hG] at hg'
  exact kill_rank0 (c := 16) (R := 8) hp hn (by norm_num) hR hg'

theorem fam_F4 {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .F4) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  exfalso
  have hn : 1 ≤ lab.n := by
    unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at hlab
    rw [ht] at hlab
    exact hlab.1
  have hex : ¬ exempt107 lab := by
    intro h; unfold exempt107 at h; simp [ht] at h
  have hg' := hg.resolve_left hex
  have hU := upA_of_plain (p := p) (lab := lab) (by simp [ht])
  have hG : twoRankLow107 lab = 7 * lab.n := by simp only [twoRankLow107, ht]
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 4 := by
    unfold rk2Mult
    simp only [ht]
    unfold rk2Cnt
    exact le_trans List.countP_le_length (by simp)
  rw [hU, hG] at hg'
  exact kill_rank0 (c := 7) (R := 4) hp hn (by norm_num) hR hg'

theorem fam_twE6 {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .twE6) (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  exfalso
  have hn : 1 ≤ lab.n := by
    unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at hlab
    rw [ht] at hlab
    exact hlab.1
  have hex : ¬ exempt107 lab := by
    intro h; unfold exempt107 at h; simp [ht] at h
  have hg' := hg.resolve_left hex
  have hU := upA_of_plain (p := p) (lab := lab) (by simp [ht])
  have hG : twoRankLow107 lab = 9 * lab.n := by simp only [twoRankLow107, ht]
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 6 := by
    unfold rk2Mult
    simp only [ht]
    unfold rk2Cnt
    exact le_trans List.countP_le_length (by simp)
  rw [hU, hG] at hg'
  exact kill_rank0 (c := 9) (R := 6) hp hn (by norm_num) hR hg'

theorem fam_G2 {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .G2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  exfalso
  have hn : 2 ≤ lab.n := by
    unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at hlab
    rw [ht] at hlab
    exact hlab.2.2
  have hex : ¬ exempt107 lab := by
    intro h; unfold exempt107 at h; simp [ht] at h
  have hg' := hg.resolve_left hex
  have hU := upA_of_plain (p := p) (lab := lab) (by simp [ht])
  have hG : twoRankLow107 lab = 3 * lab.n := by simp only [twoRankLow107, ht]
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 2 := by
    unfold rk2Mult
    simp only [ht]
    exact rk2_G2_le
  have he : (if p ∣ lab.n then 1 else 0) ≤ 1 := by split_ifs <;> omega
  rw [hU, hG] at hg'
  exact arith_G2 lab.n _ _ hn he hR hg'

theorem fam_twB2 {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .twB2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  exfalso
  have hU := upA_of_plain (p := p) (lab := lab) (by simp [ht])
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 1 := by
    unfold rk2Mult
    simp only [ht]
    exact rk2Cnt_twB2_le_one _
  have he : (if p ∣ lab.n then 1 else 0) ≤ 1 := by split_ifs <;> omega
  rw [hU] at hA
  omega

theorem fam_twF4 {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .twF4) (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  exfalso
  have hn : 3 ≤ lab.n := by
    unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at hlab
    rw [ht] at hlab
    exact hlab.2.2.2
  have hex : ¬ exempt107 lab := by
    intro h; unfold exempt107 at h; simp [ht] at h
  have hg' := hg.resolve_left hex
  have hU := upA_of_plain (p := p) (lab := lab) (by simp [ht])
  have hG : twoRankLow107 lab = 2 * lab.n := by simp only [twoRankLow107, ht]
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 2 := by
    unfold rk2Mult
    simp only [ht]
    exact rk2_twF4_le
  have he : (if p ∣ lab.n then 1 else 0) ≤ 1 := by split_ifs <;> omega
  rw [hU, hG] at hg'
  exact arith_twF4 lab.n _ _ hn he hR hg'

theorem fam_triD4 {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .triD4) (hp : p.Prime)
    (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p) (hg : exempt107 lab ∨ twoRankLow107 lab ≤ upA107 lab p + 2) :
    p = 3 ∧ survivor107 lab := by
  have hn : 1 ≤ lab.n := by
    unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at hlab
    rw [ht] at hlab
    exact hlab.1
  have hex : ¬ exempt107 lab := by
    intro h; unfold exempt107 at h; simp [ht] at h
  have hg' := hg.resolve_left hex
  have hG : twoRankLow107 lab = 5 * lab.n := by simp only [twoRankLow107, ht]
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 2 := by
    unfold rk2Mult
    simp only [ht]
    exact rk2_triD4_le
  unfold upA107 at hA hg'
  rw [hG] at hg'
  obtain ⟨he1, -⟩ := e_facts hp hp2 hn
  have hbE : (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  have hn1 : lab.n = 1 → (if p ∣ lab.n then 1 else 0) = 0 := by
    intro h1
    rw [if_neg]
    rw [h1]
    intro hd
    exact hp.ne_one (Nat.dvd_one.1 hd)
  have hb1 : (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) = 1 → p = 3 := by
    intro h
    by_cases hc : p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4)
    · exact hc.1
    · rw [if_neg hc] at h
      omega
  generalize (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0) = b at hA hg' hbE hb1
  generalize (if p ∣ lab.n then 1 else 0) = e at hA hg' he1 hn1
  obtain ⟨hn1', hb⟩ := arith_triD4 lab.n _ e b hn he1 hbE hn1 hR hA hg'
  refine ⟨hb1 hb, Or.inl ⟨hn1', Or.inr (Or.inr (Or.inr (Or.inr ht)))⟩⟩

theorem fam_der {lab : GLALabel} {p : ℕ} (hlab : GLAInLambda2 lab) (ht : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : 3 ≤ upA107 lab p) : p = 3 ∧ survivor107 lab := by
  exfalso
  have hn : lab.n = 1 := by
    unfold GLAInLambda2 CFSG.Assembly.LargeEvenInLambda2 at hlab
    rcases ht with h | h | h <;> rw [h] at hlab <;> exact hlab.2.2
  have hU := upA_of_plain (p := p) (lab := lab) (by rcases ht with h | h | h <;> simp [h])
  have he0 : (if p ∣ lab.n then 1 else 0) = 0 := by
    rw [if_neg]
    rw [hn]
    intro hd
    exact hp.ne_one (Nat.dvd_one.1 hd)
  have hR : rk2Mult lab (rk2Ord p lab.n) ≤ 2 := by
    rcases ht with h | h | h
    · unfold rk2Mult
      simp only [h]
      have hpos := rk2Ord_pos hp hp2 lab.n
      split_ifs with hm
      · exact Nat.div_le_of_le_mul (by omega)
      · exact le_trans (Nat.div_le_self _ _) (by norm_num)
    · unfold rk2Mult
      simp only [h]
      exact rk2_G2_le
    · unfold rk2Mult
      simp only [h]
      exact rk2_twF4_le
  rw [hU, he0] at hA
  omega

end CFSG.LocalAnalysis.GLTheoremA

end
