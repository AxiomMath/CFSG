module

public import CFSG.HardMathSupport.C14F4LatticeCheck

public section

namespace CFSG.HardMathSupport.C14F4LatticeCheck

theorem linesOK_0 : ((f4Lines).take 40).all (fun k => latOK [k]) = true := by decide +kernel

theorem linesOK_1 : (((f4Lines).drop 40).take 40).all (fun k => latOK [k]) = true := by decide +kernel

theorem linesOK_2 : (((f4Lines).drop 40).drop 40).all (fun k => latOK [k]) = true := by decide +kernel

theorem linesOK_eq : linesOK = true := by
  unfold linesOK
  refine all_eq_true_of_take_drop 40 linesOK_0 ?_
  refine all_eq_true_of_take_drop 40 linesOK_1 ?_
  exact linesOK_2

theorem rank3OK_eq : rank3OK = true := by decide +kernel

end CFSG.HardMathSupport.C14F4LatticeCheck
