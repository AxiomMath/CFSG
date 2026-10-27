module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
  CFSG.EvenSporadicStandard.Induction

@[expose] def HSOuterOutcomeFive (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Equiv.Perm (Fin 10)) ∨ Nonempty (X ≃* MulAut (Carrier .HS))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

end CFSG.EvenSporadicStandard.HSStd
