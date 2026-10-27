module

import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.RegularModuleThree

section CommGroupLemmas

variable {A : Type*} [CommGroup A]

theorem pow_eq_pow_of_natCast_eq {z : A} (hz : z ^ 3 = 1) {a b : ℕ} (h : (a : ZMod 3) = b) :
    z ^ a = z ^ b := by
  rw [pow_eq_pow_mod a hz, pow_eq_pow_mod b hz, (ZMod.natCast_eq_natCast_iff' a b 3).mp h]

end CommGroupLemmas

end CFSG.RegularModuleThree
