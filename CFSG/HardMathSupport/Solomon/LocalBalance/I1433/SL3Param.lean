module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433SameField
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open

private def ordSL3 (q : ℕ) : ℕ := q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)

private def ordSU3 (q : ℕ) : ℕ := q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)

private theorem pow_lt_pow_of_lt {a b : ℕ} (hab : a < b) (n : ℕ) (hn : n ≠ 0) : a ^ n < b ^ n :=
  Nat.pow_lt_pow_left hab hn

private theorem ordSL3_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) : ordSL3 a < ordSL3 b := by
  unfold ordSL3
  have h1 := pow_lt_pow_of_lt hab 3 (by norm_num)
  have h2 := pow_lt_pow_of_lt hab 2 (by norm_num)
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ha3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2' : a ^ 2 - 1 < b ^ 2 - 1 := by omega
  have h3' : a ^ 3 - 1 < b ^ 3 - 1 := by omega
  exact mul_lt_mul'' (mul_lt_mul'' h1 h2' (Nat.zero_le _) (Nat.zero_le _)) h3' (Nat.zero_le _)
    (Nat.zero_le _)

private theorem ordSU3_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) : ordSU3 a < ordSU3 b := by
  unfold ordSU3
  have h1 := pow_lt_pow_of_lt hab 3 (by norm_num)
  have h2 := pow_lt_pow_of_lt hab 2 (by norm_num)
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2' : a ^ 2 - 1 < b ^ 2 - 1 := by omega
  have h3' : a ^ 3 + 1 < b ^ 3 + 1 := by omega
  exact mul_lt_mul'' (mul_lt_mul'' h1 h2' (Nat.zero_le _) (Nat.zero_le _)) h3' (Nat.zero_le _)
    (Nat.zero_le _)

private theorem ordSL3_lt_ordSU3 {a : ℕ} (ha : 2 ≤ a) : ordSL3 a < ordSU3 a := by
  unfold ordSL3 ordSU3
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have hpos : 0 < a ^ 3 * (a ^ 2 - 1) := Nat.mul_pos (pow_pos (by omega) 3) (by omega)
  exact Nat.mul_lt_mul_of_pos_left (by omega) hpos

private theorem ordSU3_lt_ordSL3_succ {a : ℕ} (ha : 2 ≤ a) : ordSU3 a < ordSL3 (a + 1) := by
  unfold ordSL3 ordSU3
  have h1 : a ^ 3 < (a + 1) ^ 3 := pow_lt_pow_of_lt (by omega) 3 (by norm_num)
  have h2 : a ^ 2 < (a + 1) ^ 2 := pow_lt_pow_of_lt (by omega) 2 (by norm_num)
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2' : a ^ 2 - 1 < (a + 1) ^ 2 - 1 := by omega
  have h3' : a ^ 3 + 1 < (a + 1) ^ 3 - 1 := by
    have : (a + 1) ^ 3 = a ^ 3 + 3 * a ^ 2 + 3 * a + 1 := by ring
    omega
  exact mul_lt_mul'' (mul_lt_mul'' h1 h2' (Nat.zero_le _) (Nat.zero_le _)) h3' (Nat.zero_le _)
    (Nat.zero_le _)

private theorem ordSL3_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : ordSL3 a ≤ ordSL3 b := by
  rcases eq_or_lt_of_le hab with rfl | h
  · exact le_rfl
  · exact (ordSL3_lt ha h).le

private theorem card_of_isSL3EpsOver {Y : Type} [Group Y] {q : ℕ} (h : IsSL3EpsOver Y q) :
    2 ≤ q ∧ (Nat.card Y = ordSL3 q ∨ Nat.card Y = ordSU3 q) := by
  rcases h.1 with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    refine ⟨hF ▸ h2, Or.inl ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three F, hF, ordSL3,
      mul_assoc]
  · have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    have hq : 2 ≤ q := by
      by_contra hlt
      push Not at hlt
      interval_cases q <;> simp_all
    refine ⟨hq, Or.inr ?_⟩
    rw [Nat.card_congr e.toEquiv,
      CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hF, ordSU3]

theorem IsSL3EpsOver.param_eq {Y : Type} [Group Y] {q q' : ℕ} (h : IsSL3EpsOver Y q)
    (h' : IsSL3EpsOver Y q') : q = q' := by
  obtain ⟨hq, hY⟩ := card_of_isSL3EpsOver h
  obtain ⟨hq', hY'⟩ := card_of_isSL3EpsOver h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rcases hY with hY | hY <;> rcases hY' with hY' | hY'
    · exact (ordSL3_lt hq hlt).ne (hY.symm.trans hY')
    · exact ((ordSL3_lt hq hlt).trans (ordSL3_lt_ordSU3 hq')).ne (hY.symm.trans hY')
    · have := (ordSU3_lt_ordSL3_succ hq).trans_le (ordSL3_le (by omega) (Nat.succ_le_of_lt hlt))
      exact this.ne (hY.symm.trans hY')
    · exact (ordSU3_lt hq hlt).ne (hY.symm.trans hY')
  · rcases hY with hY | hY <;> rcases hY' with hY' | hY'
    · exact (ordSL3_lt hq' hlt).ne (hY'.symm.trans hY)
    · have := (ordSU3_lt_ordSL3_succ hq').trans_le (ordSL3_le (by omega) (Nat.succ_le_of_lt hlt))
      exact this.ne (hY'.symm.trans hY)
    · exact ((ordSL3_lt hq' hlt).trans (ordSL3_lt_ordSU3 hq)).ne (hY'.symm.trans hY)
    · exact (ordSU3_lt hq' hlt).ne (hY'.symm.trans hY)

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
