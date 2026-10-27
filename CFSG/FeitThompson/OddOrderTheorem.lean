module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.FeitThompson.OddOrder.OddOrderTheoremUnconditional

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem isSolvable_of_odd_natCard (G : Type*) [Group G] [Finite G] (hG : Odd (Nat.card G)) :
    Group.IsSolvable G :=
  Results.FT_odd_order_solvable G hG

end CFSG.FeitThompson
