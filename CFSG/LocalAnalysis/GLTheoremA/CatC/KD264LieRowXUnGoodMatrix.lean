module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesMatrix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

open Matrix CFSG.RankThree.PartTwo.Sec21.Tables

variable {K : Type*} [Field K] {N : ℕ}

@[expose] def IsBlock (C : Set (Fin N)) (M : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ a b, ((a ∈ C ∧ b ∉ C) ∨ (a ∉ C ∧ b ∈ C)) → M a b = 0

theorem diag_mul_apply {d M : Matrix (Fin N) (Fin N) K} (hd : ∀ i j, i ≠ j → d i j = 0)
    (a b : Fin N) : (d * M) a b = d a a * M a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro k _ hk
    rw [hd a k (Ne.symm hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem mul_diag_apply {d M : Matrix (Fin N) (Fin N) K} (hd : ∀ i j, i ≠ j → d i j = 0)
    (a b : Fin N) : (M * d) a b = M a b * d b b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · intro k _ hk
    rw [hd k b hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem isBlock_entry_of_commute {d M : Matrix (Fin N) (Fin N) K} (hd : ∀ i j, i ≠ j → d i j = 0)
    (hcomm : d * M = M * d) {a b : Fin N} (hab : d a a ≠ d b b) : M a b = 0 := by
  have e := congrFun (congrFun hcomm a) b
  rw [diag_mul_apply hd, mul_diag_apply hd] at e
  have h2 : (d a a - d b b) * M a b = 0 := by
    rw [sub_mul, e, mul_comm (M a b) (d b b), sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) hab
  · exact h

theorem isBlock_of_commute {C : Set (Fin N)} {M : Matrix (Fin N) (Fin N) K}
    (hsep : ∀ a b, ((a ∈ C ∧ b ∉ C) ∨ (a ∉ C ∧ b ∈ C)) →
      ∃ d : Matrix (Fin N) (Fin N) K, (∀ i j, i ≠ j → d i j = 0) ∧ d * M = M * d ∧
        d a a ≠ d b b) :
    IsBlock C M := by
  intro a b hab
  obtain ⟨d, hd, hcomm, hne⟩ := hsep a b hab
  exact isBlock_entry_of_commute hd hcomm hne

theorem commute_of_const {C : Set (Fin N)} {d H : Matrix (Fin N) (Fin N) K}
    (hd : ∀ i j, i ≠ j → d i j = 0)
    (hconst : ∀ a b, a ∈ C → b ∈ C → d a a = d b b)
    (hH : IsIdOutside C H) : d * H = H * d := by
  ext a b
  rw [diag_mul_apply hd, mul_diag_apply hd]
  by_cases hab : a = b
  · subst hab
    exact mul_comm _ _
  · by_cases hC : a ∈ C ∧ b ∈ C
    · rw [hconst a b hC.1 hC.2, mul_comm]
    · have hH0 : H a b = 0 := by
        rw [hH a b (not_and_or.mp hC), Matrix.one_apply_ne hab]
      rw [hH0, mul_zero, zero_mul]

theorem isIdOutside_conj {C : Set (Fin N)} {M N' H : Matrix (Fin N) (Fin N) K}
    (hM : IsBlock C M) (hN : IsBlock C N') (hMN : M * N' = 1) (hH : IsIdOutside C H) :
    IsIdOutside C (M * H * N') := by
  unfold IsIdOutside at hH ⊢
  set E : Matrix (Fin N) (Fin N) K := H - 1 with hEdef
  have hE1 : ∀ k l, (k ∉ C ∨ l ∉ C) → E k l = 0 := by
    intro k l hkl
    rw [hEdef, Matrix.sub_apply, hH k l hkl, sub_self]
  have hsplit : M * H * N' = 1 + M * E * N' := by
    have h1 : M * E * N' = M * H * N' - M * N' := by
      rw [hEdef]
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    rw [h1, hMN]
    abel
  have hrow : ∀ a, a ∉ C → ∀ l, (M * E) a l = 0 := by
    intro a ha l
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ C
    · rw [hM a k (Or.inr ⟨ha, hk⟩), zero_mul]
    · rw [hE1 k l (Or.inl hk), mul_zero]
  have hcol : ∀ l, l ∉ C → ∀ a, (M * E) a l = 0 := by
    intro l hl a
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hE1 k l (Or.inr hl), mul_zero]
  intro a b hab
  rw [hsplit, Matrix.add_apply]
  have hz : (M * E * N') a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases hab with ha | hb
    · rw [hrow a ha l, zero_mul]
    · by_cases hl : l ∈ C
      · rw [hN l b (Or.inl ⟨hl, hb⟩), mul_zero]
      · rw [hcol l hl a, zero_mul]
  rw [hz, add_zero]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

end
