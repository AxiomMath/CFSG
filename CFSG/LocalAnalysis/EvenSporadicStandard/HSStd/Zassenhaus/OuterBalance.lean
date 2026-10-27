module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5A8

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open CFSG.EvenSporadicStandard.HSStd Subgroup

section OddCore

theorem oddCore_eq_bot_iff {Y : Type*} [Group Y] :
    CFSG.oddCore Y = ⊥ ↔ ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  constructor
  · intro h N hN hodd
    rw [eq_bot_iff, ← h]
    exact le_sSup ⟨hN, hodd⟩
  · intro h
    rw [CFSG.oddCore, sSup_eq_bot]
    rintro N ⟨hN, hodd⟩
    exact h N hN hodd

end OddCore

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
