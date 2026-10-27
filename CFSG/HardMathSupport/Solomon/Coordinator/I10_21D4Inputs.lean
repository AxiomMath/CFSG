module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2.Native

@[expose] def i1021InvW (w : List ℤ) : List ℤ := (w.map fun l => -l).reverse

@[expose] def i1021CommW (a b : List ℤ) : List ℤ := a ++ b ++ i1021InvW a ++ i1021InvW b

@[expose] def i1021HighRootWord : List ℤ :=
  i1021CommW (i1021CommW (i1021CommW (i1021CommW [1] [3]) [5]) [7]) [3]

@[expose] def i1021D4Word : Fin 4 → List ℤ := ![[1], [5], [7], i1021HighRootWord]

@[expose] def i1021D4Arr (i : Fin 4) : Array ℕ := omegaW (i1021D4Word i)

@[expose] def i1021D4Prod (a : Fin 4 → Fin 2) : Array ℕ :=
  (List.ofFn fun i => powArr (i1021D4Arr i) (a i : ℕ)).foldr (compA 360) (idA 360)

end CFSG.HardMathSupport.Solomon.Coordinator
