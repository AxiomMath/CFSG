module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaData

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def rowsGE (e₀ e₁ e₂ e₃ : ℕ) : Array V4 :=
  mulRows (mulRows (mulRows (powRows rowsG1 e₀) (powRows rowsG2 e₁)) (powRows rowsG3 e₂))
    (powRows rowsG4 e₃)

@[expose] def T0cols : List ℕ := [1, 3, 4, 8]

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
