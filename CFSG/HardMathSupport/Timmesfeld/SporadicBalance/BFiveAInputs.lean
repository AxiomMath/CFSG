module

public import Certificates.Data.CFSGNative.MonsterB.Primes

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

@[expose] def max15Prog (_ : Unit := ()) : List Ins :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 4 8, .mu 3 8 9, .mu 3 9 10,
    .mu 10 8 2, .pwr 14 2 3, .mu 6 7 8, .pwr 17 8 9, .iv 1 4, .mu 4 9 8, .mu 8 1 4, .mu 4 3 5,
    .mu 5 3 6, .mu 6 6 7, .mu 7 5 8, .iv 3 7, .mu 7 4 6, .mu 6 3 7, .mu 5 5 6, .mu 7 6 5,
    .iv 5 4, .mu 4 8 6, .mu 6 5 4, .iv 4 5, .mu 5 3 6, .mu 6 4 5, .mu 5 5 6, .mu 3 6 7,
    .mu 4 7 8, .mu 8 7 4, .iv 4 5, .mu 5 3 6, .mu 6 4 5, .mu 5 5 6, .mu 3 6 7, .mu 4 7 8,
    .mu 8 7 1]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
