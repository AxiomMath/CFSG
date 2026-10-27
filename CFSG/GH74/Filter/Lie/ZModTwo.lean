module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.Filter.Lie

theorem zmod_two_eq_zero_or_one : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem multiplicative_zmod_two_sq : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide

end CFSG.GH74.Filter.Lie
