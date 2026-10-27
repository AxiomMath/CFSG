module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Check

public section

namespace CFSG.EvenSporadicStandard.M22Std.E32Check

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck

@[expose] def xProp : Prop :=
  ∃ l ∈ jTabs, l ∈ s0Outer ∧ tmul l l = idTab ∧ fixF l = 4

instance : Decidable xProp := by
  unfold xProp
  infer_instance

@[expose] def xCheck : Bool := decide xProp

end CFSG.EvenSporadicStandard.M22Std.E32Check
