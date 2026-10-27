module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem orderOf_le_three_alternating_four (x : alternatingGroup (Fin 4)) : orderOf x ≤ 3 := by
  have h : ∀ y : alternatingGroup (Fin 4), y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 := by
    decide +kernel
  rcases h x with h1 | h2 | h3
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h1).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) h3

theorem orderOf_le_four_perm_four (x : Equiv.Perm (Fin 4)) : orderOf x ≤ 4 := by
  have h : ∀ y : Equiv.Perm (Fin 4), y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 4 = 1 := by
    decide +kernel
  rcases h x with h1 | h2 | h3 | h4
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h1).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h3).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) h4

theorem orderOf_le_five_alternating_five (x : alternatingGroup (Fin 5)) : orderOf x ≤ 5 := by
  have h : ∀ y : alternatingGroup (Fin 5),
      y ^ 1 = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 4 = 1 ∨ y ^ 5 = 1 := by
    decide +kernel
  rcases h x with h1 | h2 | h3 | h4 | h5
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h1).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h3).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h4).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) h5

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
