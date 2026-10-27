module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderMax
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

variable {G : Type} [Group G]

theorem altHeart_sub_aux {d : ℕ} (a b c e : altHeart d) (h : c + b = a + e) :
    a - b - (c - e) = 0 := by
  let _ : AddCommGroup (evenWeight d) := AddSubgroup.toAddCommGroup (evenWeight d)
  let _ : AddCommGroup (altHeart d) := QuotientAddGroup.Quotient.addCommGroup (evenWeightOnes d)
  have h2 : a - b - (c - e) = (a + e) - (c + b) := by abel
  exact h2.trans (sub_eq_zero.2 h.symm)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
