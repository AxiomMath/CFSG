module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqPer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqFinAc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqFinAe
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqFinBc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqFinBe
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqFinO

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

theorem cl24_final {τ τ' : StatedLieTag} {n n' j d : ℕ} (hadm : StatedLieAdmissible τ n 3 j)
    (hadm' : StatedLieAdmissible τ' n' 3 d) (hjd : j < d) (hτ : τ ≠ .twistedG2)
    (hN : lieSylowExponent τ n * j = lieSylowExponent τ' n' * d)
    (hE : j * cl24E τ n = d * cl24E τ' n')
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor τ' n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor τ' n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ)) :
    False := by
  by_cases hL : τ' = .PSL
  · subst hL
    rcases cl24_cls hadm hτ with hc | he
    · exact cl24_finPSL_cla hc hadm hadm' hjd hN hE hX
    · exact cl24_finPSL_exc he hadm hadm' hjd hN hE hX
  by_cases hU : τ' = .PSU
  · subst hU
    rcases cl24_cls hadm hτ with hc | he
    · exact cl24_finPSU_cla hc hadm hadm' hjd hN hE hX
    · exact cl24_finPSU_exc he hadm hadm' hjd hN hE hX
  · exact cl24_fin_other hL hU hadm hadm' hX

end CFSG.OddStandard.SmallF3.HypA2Leaves
