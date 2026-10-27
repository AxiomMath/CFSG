module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDefs

public section

namespace CFSG.EvenSmallLie.Child3.SelK3

open CFSG.Sporadic.Th.Native

@[expose] def m22TA : Table :=
  #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]

@[expose] def m22TB : Table :=
  #[21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]

@[expose] def m22K3Prog : String := include_str "Child3SelK3MathieuM22.txt"

@[expose] def m22K3 : Data where
  n := 22
  gens := #[m22TA, m22TB]
  regs := 36
  prog := parseProg m22K3Prog
  syl := [14, 21]
  order := 9
  reps :=
    [1, 2, 4, 6]
  wits :=
    [.v4 27 29, .v4 30 31, .v4 32 33, .v4 34 35]

@[expose] def m23TA : Table :=
  #[1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] def m23TB : Table :=
  #[15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] def m23K3Prog : String := include_str "Child3SelK3MathieuM23.txt"

@[expose] def m23K3 : Data where
  n := 23
  gens := #[m23TA, m23TB]
  regs := 38
  prog := parseProg m23K3Prog
  syl := [16, 20]
  order := 9
  reps :=
    [1, 2, 4, 6]
  wits :=
    [.v4 30 31, .v4 32 33, .v4 34 35, .v4 36 37]

@[expose] def m24TA : Table :=
  #[3, 6, 16, 0, 12, 8, 1, 14, 5, 18, 17, 20, 4, 15, 7, 13, 2, 10, 9, 23, 11, 22, 21, 19]

@[expose] def m24TB : Table :=
  #[3, 20, 8, 5, 17, 0, 6, 7, 14, 4, 10, 11, 16, 1, 2, 12, 15, 9, 23, 19, 13, 21, 18, 22]

@[expose] def m24K3Prog : String := include_str "Child3SelK3MathieuM24.txt"

@[expose] def m24K3 : Data where
  n := 24
  gens := #[m24TA, m24TB]
  regs := 41
  prog := parseProg m24K3Prog
  syl := [14, 27]
  order := 27
  reps :=
    [18, 13, 4, 7, 25]
  wits :=
    [.v4 32 34, .z4 35, .v4 36 37, .v4 38 39, .z4 40]

end CFSG.EvenSmallLie.Child3.SelK3
