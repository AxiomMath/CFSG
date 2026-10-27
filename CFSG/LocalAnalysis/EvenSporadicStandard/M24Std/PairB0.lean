module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PinnedB

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.QuasithinUnique.Setup.X1

@[expose] def B0ListData : Prop :=
  m24B0l.length = 16 ∧ m24B0l.Nodup ∧ (1 : S24) ∈ m24B0l ∧
    (∀ x ∈ m24B0l, ∀ y ∈ m24B0l, x * y ∈ m24B0l) ∧ (∀ x ∈ m24B0l, x * x = 1) ∧
    (∀ x ∈ m24B0l, ∀ y ∈ m24B0l, x * y = y * x)

instance : Decidable B0ListData := by unfold B0ListData; infer_instance

end CFSG.EvenSporadicStandard.M24Std
