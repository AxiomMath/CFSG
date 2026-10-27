module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Vocab
public import Certificates.Data.GH23Perm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

@[expose] def GH23Spec (P : Subgroup (Equiv.Perm (Fin 8))) : Prop :=
  IsSolvable ↥P ∨ ¬ NoNormalTwo P ∨ GH23Concl ↥P

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
