module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PinnedB

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def splitBPt : Fin 24 := 0

@[expose] def splitBWord : List ℤ := [1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2]

@[expose] def SplitBCentData : Prop :=
  (∀ b ∈ m24B0l, ∀ c ∈ m24B0l, b * c = c * b) ∧
  (∀ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) splitBPt = splitBPt → b = 1) ∧
  (∀ q : Fin 24, (∀ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) q = q → b = 1) →
    ∃ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) splitBPt = q) ∧
  ∀ i : Fin 24, i.val < 7 → ∃ b ∈ m24B0l,
    (b : Equiv.Perm (Fin 24)) splitBPt = (m24Cj splitBWord : Equiv.Perm (Fin 24)) i

instance : Decidable SplitBCentData := by unfold SplitBCentData; infer_instance

end CFSG.EvenSporadicStandard.M24Std
