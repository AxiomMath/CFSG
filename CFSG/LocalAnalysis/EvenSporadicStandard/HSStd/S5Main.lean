module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction

theorem card_eq_of_isSporadic {X Y : Type} [Group X] [Group Y] {s : TauCeti.SporadicName}
    (hX : IsSporadic X s) (hY : IsSporadic Y s) : Nat.card X = Nat.card Y := by
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ := hY
  exact Nat.card_congr (e.trans f.symm).toEquiv

end CFSG.EvenSporadicStandard.HSStd
