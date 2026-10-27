module

public import CFSG.ClassicalInvolution.Q3.Q3T6YSym
public import CFSG.ClassicalInvolution.Q3.Q3T6YTriv
public import CFSG.ClassicalInvolution.Q3.Q3T6XBal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
  CFSG.ClassicalInvolution.Q3.Q3T6X

variable {F : Type} [Group F] [Finite F]

theorem diagInputTrivOn_all (F : Type) [Group F] [Finite F] (S : Set F) : DiagInputTrivOn F S :=
  diagInputTrivOn_of_noTrivialSwapOn (noTrivialSwapOn_all F S)

theorem fusion3MinOn_all (h368 : Bal368 F) (S : Set F) : Fusion3MinOn F S :=
  fusion3MinOn_of_bal368 h368 (diagInputTrivOn_all F S)

theorem fusion3Min_of_bal368 (h368 : Bal368 F) : Fusion3Min F where
  symOuter := fun {_ _ x y} hX hY hxY hout =>
    (fusion3MinOn_all h368 Set.univ).symOuter hX hY (Set.mem_univ x) (Set.mem_univ y) hxY hout
  diagNorm := fun {_ r u} hQ hu2 hur hne {_} hI hrI {_} hq hq2 hqc =>
    (fusion3MinOn_all h368 Set.univ).diagNorm hQ (Set.mem_univ r) (Set.mem_univ u) hu2 hur hne hI
      hrI hq hq2 hqc

theorem fusion3Min_all (F : Type) [Group F] [Finite F] : Fusion3Min F :=
  fusion3Min_of_bal368 (bal368_all F)

theorem fusion3MinAll : Fusion3MinAll :=
  fun G _ _ _ _ => fusion3Min_all G

end CFSG.ClassicalInvolution.Q3.Q3T6Y
