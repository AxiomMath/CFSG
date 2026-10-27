module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Code

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

@[expose] def gh23Sub (gens : List ℕ) : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure {σ | gh23Code σ ∈ gens}

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
