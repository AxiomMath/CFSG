module

public import CFSG.HardMathSupport.U4FF.ClassClassif
public import CFSG.HardMathSupport.U4FF.ClassDatum

public section

namespace CFSG.HardMathSupport.U4FF

section Iface

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def curtisIface (hK : Nat.card K = (2 ^ n) ^ 2) : CurtisIface K n hK where
  D := datum4 hK
  C := cover4 hK
  R := rank1_4 hK
  hU := cover4_lU hK
  hH := datum4_H hK
  hh0 := rank1_4_hh0 hK
  hh1 := rank1_4_hh1 hK
  hodd := hodd4 hK
  hsplit := fun k => splitOver4 hK k

end Iface

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem classif_holds (hK : Nat.card K = (2 ^ n) ^ 2) : Classif K n :=
  classif_of_iface (curtisIface hK)

end Main

end CFSG.HardMathSupport.U4FF
