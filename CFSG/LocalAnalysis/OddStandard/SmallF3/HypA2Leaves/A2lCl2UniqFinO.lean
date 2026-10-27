module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDiv

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

theorem cl24_fin_other {τ τ' : StatedLieTag} {n n' j d : ℕ} (hτ' : τ' ≠ .PSL) (hτ'' : τ' ≠ .PSU)
    (hadm : StatedLieAdmissible τ n 3 j) (hadm' : StatedLieAdmissible τ' n' 3 d)
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor τ' n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor τ' n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ)) :
    False := by
  have h1 := cl24_size_of_digit hX
  have h2 := cl24_D_le_four hadm' hτ' hτ''
  have h3 := cl24_D_le hadm
  have hj : 1 ≤ j := hadm.2.1
  have h4 : 3 ≤ 3 ^ j := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  rw [cl24_pow_two_mul] at h1
  nlinarith

end CFSG.OddStandard.SmallF3.HypA2Leaves
