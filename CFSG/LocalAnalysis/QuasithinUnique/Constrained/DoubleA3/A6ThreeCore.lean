module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique.A6Facts

theorem aut_three_check : Core.autL.all (fun c =>
    Core.cpow c 3 != Core.cid || Core.pslLit.contains c) = true := by
  decide +kernel

theorem pow_nine_check : Core.pslLit.all (fun c =>
    Core.cpow c 9 != Core.cid || Core.cpow c 3 == Core.cid) = true := by
  decide +kernel

end CFSG.QuasithinUnique.DoubleA3
