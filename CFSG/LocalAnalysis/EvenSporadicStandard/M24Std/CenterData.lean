module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24CheckInputs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

@[expose] def centerList : List ↥NativeSporadic.M24 :=
  m24rl.filter fun x => decide (∀ y ∈ m24rl, x * y = y * x)

@[expose] def CenterData : Prop := centerList.length = 2

instance : Decidable CenterData := by
  unfold CenterData
  infer_instance

end CFSG.EvenSporadicStandard.M24Std
