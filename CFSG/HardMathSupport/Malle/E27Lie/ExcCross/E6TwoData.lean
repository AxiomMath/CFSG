module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNE6Two
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcIntSolve
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.PairClosure

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Curtis.UnitaryLevi (Smat solve_int_fpf wordW wordW_append
  wordW_eq_of_matrix)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross (laE6 lbE6 wE6)

noncomputable abbrev ATw6 (l : List (Fin Tag.E6.rank)) : Matrix (Fin 6) (Fin 6) ℤ :=
  ((l.reverse.map (Smat Tag.E6)).prod).transpose

@[expose] def bK6 : Matrix (Fin 6) (Fin 4) ℤ := !![1, 0, 0, 0; 2, -2, -3, -4; -2, 0, 1, 2; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
@[expose] def Lk6 : Matrix (Fin 4) (Fin 6) ℤ := !![1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
noncomputable abbrev R6 (l : List (Fin Tag.E6.rank)) : Matrix (Fin 4) (Fin 4) ℤ :=
  Lk6 * ATw6 l * bK6

@[expose] def e6XAB : List (Fin Tag.E6.rank) := laE6 ++ lbE6

@[expose] def e6XAB2 : List (Fin Tag.E6.rank) := laE6 ++ lbE6 ++ lbE6

theorem e6A_a_data :
    (1 - R6 lbE6 = (1 - R6 laE6) * !![0, 0, 0, 0; 2, 0, 0, -2; 0, 0, 0, 0; 0, 0, 0, 0] +
      !![1, 0, -1, -1; 0, 0, 0, 0; 0, 0, 0, 0; -1, 0, 1, 2] * (1 + R6 laE6 + R6 laE6 * R6 laE6)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 laE6).mulVec ![1, 0, 0, -1]) i - ![1, 0, 0, -1] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 laE6).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) ∧
    (![1, 0, 0, -1] : Fin 4 → ℤ) 0 = 1 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 0 = 0 ∧
    (![1, 0, 0, -1] : Fin 4 → ℤ) 2 = 0 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem e6A_b_data :
    (1 - R6 laE6 = (1 - R6 lbE6) * !![0, -2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, -1, 0, 0] +
      !![0, 1, 0, 0; 0, 0, -1, 0; 0, 1, 1, 0; 0, 0, 0, 0] * (1 + R6 lbE6 + R6 lbE6 * R6 lbE6)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 lbE6).mulVec ![0, 1, 0, 0]) i - ![0, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 lbE6).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) ∧
    (![0, 1, 0, 0] : Fin 4 → ℤ) 1 = 1 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 1 = 0 ∧
    (![0, 1, 0, 0] : Fin 4 → ℤ) 2 = 0 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

section Weyl

noncomputable abbrev mp6 (l : List (Fin Tag.E6.rank)) : Matrix (Fin 6) (Fin 6) ℤ :=
  (l.map (Smat Tag.E6)).prod

abbrev PairOK6 (lx ly : List (Fin Tag.E6.rank)) : Prop :=
  mp6 (lx ++ lx ++ lx) = mp6 [] ∧ mp6 (ly ++ ly ++ ly) = mp6 [] ∧
    mp6 (lx ++ ly) = mp6 (ly ++ lx) ∧ mp6 lx ≠ mp6 [] ∧ mp6 ly ≠ mp6 [] ∧ mp6 ly ≠ mp6 lx ∧
    mp6 ly ≠ mp6 (lx ++ lx)

theorem wordW_pow_three_of_mp6 (l : List (Fin Tag.E6.rank))
    (h : mp6 (l ++ l ++ l) = mp6 []) : wordW Tag.E6 l ^ 3 = 1 := by
  have := wordW_eq_of_matrix Tag.E6 _ _ h
  rw [wordW_append, wordW_append] at this
  simpa [wordW, pow_succ, mul_assoc] using this

theorem ne_of_mp6_ne {l l' : List (Fin Tag.E6.rank)} (h : mp6 l ≠ mp6 l') :
    wordW Tag.E6 l ≠ wordW Tag.E6 l' := fun h' =>
  h (CFSG.HardMathSupport.Curtis.UnitaryLevi.matrix_eq_of_wordW_eq Tag.E6 l l' h')

theorem nine_dvd_card_closure_words (lx ly : List (Fin Tag.E6.rank)) (h : PairOK6 lx ly) :
    9 ∣ Nat.card (Subgroup.closure
      ({wordW Tag.E6 lx, wordW Tag.E6 ly} : Set (WeylGroup Tag.E6))) := by
  obtain ⟨hx, hy, hc, hx1, hy1, hyx, hyx2⟩ := h
  have hx3 := wordW_pow_three_of_mp6 lx hx
  have hy3 := wordW_pow_three_of_mp6 ly hy
  have hcomm : wordW Tag.E6 lx * wordW Tag.E6 ly = wordW Tag.E6 ly * wordW Tag.E6 lx := by
    have := wordW_eq_of_matrix Tag.E6 _ _ hc
    rwa [wordW_append, wordW_append] at this
  refine nine_dvd_card_closure_pair _ _ hx3 ?_ hy3 hcomm ?_
  · intro h1
    refine hx1 ?_
    exact CFSG.HardMathSupport.Curtis.UnitaryLevi.matrix_eq_of_wordW_eq Tag.E6 lx [] (by simpa [wordW] using h1)
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk3 : ∀ k : ℤ, wordW Tag.E6 lx ^ k = 1 ∨ wordW Tag.E6 lx ^ k = wordW Tag.E6 lx ∨
        wordW Tag.E6 lx ^ k = wordW Tag.E6 lx ^ 2 := by
      intro k
      have hg3 : wordW Tag.E6 lx ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
      have hk : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
      have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
      have h2 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
      have hpow : wordW Tag.E6 lx ^ k = wordW Tag.E6 lx ^ (k % 3) := by
        conv_lhs => rw [hk]
        rw [zpow_add, zpow_mul, hg3, one_zpow, one_mul]
      rw [hpow]
      obtain ⟨r, hr⟩ : ∃ r, r = k % 3 := ⟨_, rfl⟩
      rw [← hr] at h0 h2 ⊢
      interval_cases r
      · exact Or.inl (zpow_zero _)
      · exact Or.inr (Or.inl (zpow_one _))
      · exact Or.inr (Or.inr (by simp))
    rcases hk3 k with h1 | h1 | h1
    · exact ne_of_mp6_ne hy1 (by rw [← hk, h1]; simp [wordW])
    · exact ne_of_mp6_ne hyx (hk.symm.trans h1)
    · refine ne_of_mp6_ne hyx2 ?_
      rw [← hk, h1, sq, ← wordW_append]

theorem e6_hQ_a : 9 ∣ Nat.card (Subgroup.closure
    ({wordW Tag.E6 laE6, wordW Tag.E6 lbE6} : Set (WeylGroup Tag.E6))) :=
  nine_dvd_card_closure_words _ _ (by decide +kernel)

theorem e6_hQ_b : 9 ∣ Nat.card (Subgroup.closure
    ({wordW Tag.E6 lbE6, wordW Tag.E6 laE6} : Set (WeylGroup Tag.E6))) :=
  nine_dvd_card_closure_words _ _ (by decide +kernel)

end Weyl

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross

end
