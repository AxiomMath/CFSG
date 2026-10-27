module

public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.Sporadic.HNOddCore.CRec
public import CFSG.Sporadic.HNOddCore.InvRow6

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

@[expose] def JWord (w : List ℤ) : Prop := ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 18

instance (w : List ℤ) : Decidable (JWord w) := by unfold JWord; infer_instance

end CFSG.EvenSporadicStandard.TwoHS
