module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDefs
public import Certificates.Data.CFSGNative.PairSchreier.J2Data
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairMcLCertInputs
public import CFSG.Sporadic.HeldB.CertPChainData

public section

namespace CFSG.EvenSmallLie.Child3.SelK3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Sporadic.HeldB

@[expose] def j2K3Prog : String := include_str "Child3SelK3SporJ2.txt"

@[expose] def j2K3 : Data where
  n := 315
  gens := #[j2StrongArrs[0]!.map UInt32.ofNat, j2StrongArrs[1]!.map UInt32.ofNat]
  regs := 43
  prog := parseProg j2K3Prog
  syl := [26, 31]
  order := 27
  reps :=
    [18, 15, 17, 9, 25]
  wits :=
    [.v4 34 35, .v4 36 37, .v4 38 39, .v4 40 41, .z4 42]

@[expose] def hsK3Prog : String := include_str "Child3SelK3SporHS.txt"

@[expose] def hsK3 : Data where
  n := 3850
  gens := #[hsStrongArrs[0]!.map UInt32.ofNat, hsStrongArrs[1]!.map UInt32.ofNat]
  regs := 29
  prog := parseProg hsK3Prog
  syl := [12, 17]
  order := 9
  reps :=
    [1, 2, 4, 6]
  wits :=
    [.z4 25, .z4 26, .z4 27, .z4 28]

@[expose] def mclK3Prog : String := include_str "Child3SelK3SporMcL.txt"

@[expose] def mclK3 : Data where
  n := 275
  gens := #[mclStrongArrs[0]!.map UInt32.ofNat, mclStrongArrs[1]!.map UInt32.ofNat]
  regs := 81
  prog := parseProg mclK3Prog
  syl := [25, 31, 35]
  order := 729
  reps :=
    [97, 37, 110, 481, 262, 519, 109, 164, 531, 251, 314, 257, 271, 290, 512, 554, 580, 589, 717,
      724]
  wits :=
    [.z4 38, .v4 40 42, .v4 43 47, .v4 48 49, .v4 50 52, .v4 53 54, .v4 55 56, .v4 57 58, .v4 59 60,
      .v4 61 62, .v4 63 64, .v4 65 66, .v4 67 68, .z4 69, .v4 70 71, .v4 72 73, .v4 74 75,
      .v4 76 77, .v4 57 78, .v4 79 80]

@[expose] def heK3Prog : String := include_str "Child3SelK3SporHe.txt"

@[expose] def heK3 : Data where
  n := 8330
  gens := #[(heGen 0).map UInt32.ofNat, (heGen 1).map UInt32.ofNat]
  regs := 42
  prog := parseProg heK3Prog
  syl := [21, 28]
  order := 27
  reps :=
    [1, 15, 17, 8, 25]
  wits :=
    [.v4 32 34, .z4 36, .v4 37 38, .v4 39 40, .z4 41]

end CFSG.EvenSmallLie.Child3.SelK3
