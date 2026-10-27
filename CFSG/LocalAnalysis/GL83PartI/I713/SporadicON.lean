module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
import CFSG.Sporadic.ONOddCore.OuterOrder

public section

namespace GL83.I713

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem outClauseFor_sporadic_ONan
    [Finite (NativeSporadic.Carrier .ONan)] :
    OutClauseFor (NativeSporadic.Carrier .ONan) := by
  apply outClauseFor_of_card_outer_le_four
  show Nat.card (Outer NativeSporadic.ON) ≤ 4
  exact Nat.le_of_dvd (by norm_num) CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1

end GL83.I713
