module

public import CFSG.HardMathSupport.Foote.E27.SporBig
public import CFSG.HardMathSupport.Foote.E27.SporTh

public section

namespace CFSG.HardMathSupport.Foote.Proving

open CFSG.HardMathSupport.Foote.E27

section Certificates


theorem e27SporAt_th
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Th ≃*
      (TauCeti.CFSGIndex.sporadic .Th).Group)) :
    E27SporAt .Th :=
  fun _ _ _ _ _ _ _ hc hz e => hc.false_of_sporadic_th hz hbr e.some

end Certificates

end CFSG.HardMathSupport.Foote.Proving

end
