module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def powTwoTab (t : Tab) : ℕ → Tab
  | 0 => t
  | k + 1 => comp 42 (powTwoTab t k) (powTwoTab t k)

@[noinline, expose] def twoCentralOK (T gs : Array Tab) : Bool :=
  allBelow T.size fun k =>
    !(allBelow gs.size fun i => comp 42 T[k]! gs[i]! == comp 42 gs[i]! T[k]!) ||
      powTwoTab T[k]! 8 == idTab 42

end CFSG.ComponentClassification.GrSLit
