module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

@[expose] def nsS (k : ℕ) : S24 := sxT ^ k * sxS * sxT ^ (6 - k)

@[expose] def nsX : S24 := sxT * sxT

@[expose] def nsG : S24 := nsS 3 * nsS 4 * nsS 3

@[expose] def nsY : S24 := nsG * nsX * nsG

@[expose] def NonSplitCheck : Prop := nsX * nsY * nsX⁻¹ * nsY⁻¹ ∉ m24E1l

instance : Decidable NonSplitCheck := by
  unfold NonSplitCheck
  infer_instance

end CFSG.EvenSporadicStandard.M24Std.Sym6
