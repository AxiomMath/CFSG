module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

@[expose] def IsCharacteristicTwoLocal {Ambient : Type groupUniverse} [Group Ambient]
    (Local : Subgroup Ambient) : Prop :=
  Local ⊓ Subgroup.centralizer (pCoreOf 2 Local : Set Ambient) ≤ pCoreOf 2 Local

theorem characteristic_two_nontrivial_core {Ambient : Type groupUniverse} [Group Ambient]
    (Local : Subgroup Ambient) (hcharacteristic : IsCharacteristicTwoLocal Local)
    (hnontrivial : Local ≠ ⊥) : pCoreOf 2 Local ≠ ⊥ := by
  intro hcore
  apply hnontrivial
  apply le_antisymm _ bot_le
  intro element helement
  have hcentralizer : element ∈ Subgroup.centralizer (pCoreOf 2 Local : Set Ambient) := by
    rw [hcore]
    apply Subgroup.mem_centralizer_iff.mpr
    intro source hsource
    rw [Subgroup.mem_bot.mp hsource]
    simp
  exact hcore ▸ hcharacteristic ⟨helement, hcentralizer⟩

end CFSG.LargeEvenClassification.Helpers
