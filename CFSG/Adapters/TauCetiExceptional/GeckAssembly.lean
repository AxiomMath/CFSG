module

public import CFSG.Adapters.TauCetiExceptional.GeckRoots
public import CFSG.Adapters.TauCetiExceptional.Interface
public import CFSG.Adapters.TauCetiExceptional.GeckEntries

public noncomputable section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.Blueprint.Chevalley

def GeckRoots.RootData.toGeckMatch
    {τ : Tag} {t : DynkinType} {ht : t.Valid}
    (D : GeckRoots.RootData τ t ht) : GeckMatch τ t ht where
  lab := (Fintype.equivFin (t.GeckIndex ht)).symm.trans D.labelEquiv
  node := D.node
  sgn := fun _ => 1
  matrix_inl A _ i c r s := by
    simp only [Units.val_one, Int.cast_one, one_mul, mul_one, Equiv.trans_apply]
    exact GeckEntries.entry_inl_of_apply D.labelEquiv D.node i (D.e_apply i) A c r s
  matrix_inr A _ i c r s := by
    simp only [Units.val_one, Int.cast_one, one_mul, mul_one, Equiv.trans_apply]
    exact GeckEntries.entry_inr_of_apply D.labelEquiv D.node i (D.f_apply i) A c r s

end CFSG.TauCetiBridge
