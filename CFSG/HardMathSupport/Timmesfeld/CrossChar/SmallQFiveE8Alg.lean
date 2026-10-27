module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

theorem eq_add_neg_smul_of_sub_eq {a b f : Fin 4 → ZMod 5} {t : ZMod 5} (h : a - b = t • f) :
    b = a + (-t) • f := by
  funext j
  have h1 := congrFun h j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -h1

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
