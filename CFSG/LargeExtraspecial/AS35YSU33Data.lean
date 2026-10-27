module

public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.LargeExtraspecial.AS35YS

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

@[expose] def u33ElemCheck : Bool :=
  (elemsT QP).all fun d => !(d * d == 1) || d == 1 ||
    ((elemsT QA).all fun e => !(e * e == 1) || e == 1 || e == d || !(e * d == d * e) ||
      (elemsT QP).any fun c => c * d == d * c && !(e * (c * e * c⁻¹) == c * e * c⁻¹ * e))

end CFSG.LargeExtraspecial.AS35YS
