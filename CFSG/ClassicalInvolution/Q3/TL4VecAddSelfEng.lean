module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init

public section
namespace CFSG.ClassicalInvolution.Q3.TL4

theorem vec_add_self_gen (v : Fin 3 → ZMod 2) : v + v = 0 :=
  funext fun i => by
    show v i + v i = 0
    generalize v i = x
    revert x
    decide

end CFSG.ClassicalInvolution.Q3.TL4
