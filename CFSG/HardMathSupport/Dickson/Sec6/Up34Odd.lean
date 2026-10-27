module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Two
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance

theorem characteristic_ne_two_of_not_isCharTwoLieIndex {d : TauCeti.LieTypeIndex}
    (h : ¬ IsCharTwoLieIndex d) : d.characteristic ≠ 2 := by
  cases d <;> simp_all [IsCharTwoLieIndex]

section Assembly

theorem three_or_five_le_of_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : r = 3 ∨ 5 ≤ r := by
  by_contra h
  push Not at h
  have h2 := hr.two_le
  have : r = 4 := by omega
  subst this
  exact absurd hr (by norm_num)

end Assembly

end CFSG.HardMathSupport.Dickson.Sec6
