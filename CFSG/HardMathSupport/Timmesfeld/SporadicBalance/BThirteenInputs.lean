module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Primes
public meta import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

@[expose] def b13Prog (_ : Unit := ()) : List Ins :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 4 5, .mu 3 5 6, .mu 6 5 7, .pwr 9 7 8, .mu 1 8 6, .pwr 13 6 9,
    .iv 3 6, .mu 8 6 5, .mu 8 3 6, .mu 5 6 8, .pwr 5 8 5, .mu 3 5 10, .mu 9 10 11, .mu 11 10 12,
    .mu 11 12 13, .mu 11 13 14, .mu 14 11 15, .mu 15 12 16, .mu 11 16 17, .mu 14 16 18,
    .pwr 15 18 19, .pwr 17 17 20, .mu 10 9 12, .iv 12 13, .mu 13 11 12, .pwr 6 12 13,
    .mu 10 13 11, .mu 9 14 12, .mu 14 9 13, .iv 13 15, .mu 15 12 13, .pwr 6 13 15, .mu 14 15 12,
    .pwr 4 4 16, .iv 16 17, .mu 17 9 18, .mu 16 20 21, .mu 18 21 20, .pwr 7 20 21, .mu 21 17 22,
    .iv 22 23, .mu 23 19 24, .mu 24 22 19, .mu 12 11 1, .mu 11 12 13, .mu 13 19 2, .iv 1 25,
    .iv 2 26, .mu 1 2 27, .pwr 2 27 28, .mu 28 25 29, .mu 29 26 30, .pwr 2 30 31, .pwr 13 30 32,
    .pwr 2 25 33, .mu 33 2 34, .mu 34 25 35, .mu 35 2 36, .mu 36 25 37, .pwr 2 2 38,
    .mu 37 38 39, .pwr 13 39 40, .pwr 3 2 41, .mu 41 25 42, .pwr 13 42 43, .mu 32 40 44,
    .mu 40 43 45, .mu 43 40 46, .mu 40 43 47, .mu 47 40 48, .iv 48 49, .mu 49 1 50, .mu 32 43 51,
    .iv 51 52, .mu 52 2 53, .iv 50 54, .iv 53 55, .pwr 4 50 56, .mu 56 53 57, .pwr 2 54 58,
    .mu 57 58 59, .mu 59 55 60, .mu 60 50 61, .mu 61 55 62, .pwr 3 50 63, .mu 62 63 64,
    .pwr 2 53 65, .mu 64 65 66, .mu 66 50 67, .mu 67 53 68, .mu 68 50 69, .mu 69 55 70,
    .mu 70 50 71, .mu 71 55 72, .mu 72 50 73, .pwr 2 55 74, .mu 73 74 75, .mu 75 54 76,
    .mu 76 65 77, .mu 77 54 78, .mu 78 74 79, .pwr 3 54 80, .mu 79 80 81]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
