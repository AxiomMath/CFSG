module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Primes
public meta import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

@[expose] def b7EProg (_ : Unit := ()) : List Ins :=
  [.mu 1 2 3, .mu 3 2 4, .pwr 14 3 2, .mu 2 4 3, .pwr 19 3 2, .mu 1 2 4, .pwr 3 4 1, .mu 3 1 4,
    .mu 4 3 2, .mu 2 1 4, .mu 4 3 2, .mu 2 3 4, .pwr 33 4 2, .iv 3 4, .iv 3 5, .mu 1 3 6,
    .mu 6 3 7, .mu 7 3 6, .mu 6 3 7, .mu 7 1 6, .mu 6 4 7, .mu 7 5 4, .pwr 10 4 5, .pwr 14 4 7,
    .iv 3 4, .iv 3 6, .iv 3 8, .iv 3 9, .iv 3 10, .iv 3 11, .mu 1 3 12, .mu 12 3 13, .mu 13 3 12,
    .mu 12 1 13, .mu 13 4 12, .mu 12 6 13, .mu 13 1 12, .mu 12 8 13, .mu 13 9 12, .mu 12 10 13,
    .mu 13 11 12, .mu 12 1 13, .mu 13 3 12, .mu 12 1 13, .mu 13 3 12, .pwr 21 12 13, .iv 3 12,
    .iv 3 11, .iv 3 10, .iv 3 9, .iv 3 8, .iv 3 6, .mu 3 3 4, .mu 4 1 14, .mu 14 12 4,
    .mu 4 1 12, .mu 12 3 4, .mu 4 3 12, .mu 12 3 4, .mu 4 1 12, .mu 12 11 4, .mu 4 1 11,
    .mu 11 3 4, .mu 4 1 11, .mu 11 10 4, .mu 4 9 11, .mu 11 1 9, .mu 9 8 11, .mu 11 1 8,
    .mu 8 6 11, .mu 11 1 8, .iv 8 11, .mu 11 13 6, .mu 6 8 11, .iv 7 8, .pwr 2 8 6, .pwr 2 7 8,
    .mu 6 11 13, .mu 13 8 6, .iv 11 13, .iv 7 8, .iv 7 9, .iv 7 4, .iv 7 10, .iv 7 12, .iv 7 14,
    .iv 7 15, .iv 7 16, .iv 7 17, .iv 7 18, .iv 7 19, .mu 13 7 20, .mu 20 11 13, .mu 13 7 20,
    .mu 20 11 13, .mu 13 8 20, .mu 20 11 13, .mu 13 9 20, .mu 20 11 9, .mu 9 7 20, .mu 20 7 9,
    .mu 9 11 20, .mu 20 7 9, .mu 9 11 20, .mu 20 4 9, .mu 9 11 20, .mu 20 10 9, .mu 9 11 10,
    .mu 10 12 9, .mu 9 11 12, .mu 12 14 9, .mu 9 11 12, .mu 12 15 9, .mu 9 11 12, .mu 12 16 9,
    .mu 9 11 16, .mu 16 17 9, .mu 9 11 16, .mu 16 7 9, .mu 9 11 16, .mu 16 18 9, .mu 9 19 16,
    .mu 16 11 19, .mu 19 7 16]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
