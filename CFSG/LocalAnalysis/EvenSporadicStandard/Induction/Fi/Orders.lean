module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Defs
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Fi24.Simple

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.Blueprint.NativeSporadic

theorem fiOrders :
    FiOrders := by
  have h22 : Nat.card (Carrier .Fi22) = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22
  have h23 : Nat.card (Carrier .Fi23) = 4089470473293004800 := CFSG.Sporadic.Fi23.card_Fi23
  have h24 : Nat.card (Carrier .Fi24Prime) = Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime :=
    rfl
  refine ⟨by rw [h22, h23]; norm_num, ?_⟩
  rw [h23, h24, CFSG.Sporadic.Fi24.card_Fi24prime]
  norm_num

end CFSG.EvenSporadicStandard.Induction.Fi
