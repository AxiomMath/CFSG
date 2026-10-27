
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Three
public import Certificates.Certificate13622

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open scoped Pointwise

namespace Fi23Sylow

section Tables

end Tables

section Enumeration

variable {G : Array Table} {P : Array (ℕ × ℕ)} {img : Array ℕ}
  {N : ℕ}

end Enumeration

section Main

theorem fi23ThreeTranspositionFixed : Fi23ThreeTranspositionFixed :=
  fun s hs => Certificates.certificate13622 s hs

end Main

end Fi23Sylow

open Fi23Sylow

theorem sporadicOPrimeHolds_Fi23_three :
    SporadicOPrimeHolds .Fi23 3 :=
  sporadicOPrimeHolds_Fi23_three_of_fixed fi23ThreeTranspositionFixed

theorem sporadicOnePairHolds_Fi23_three :
    SporadicOnePairHolds .Fi23 3 :=
  sporadicOnePairHolds_Fi23_three_of_fixed fi23ThreeTranspositionFixed

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
