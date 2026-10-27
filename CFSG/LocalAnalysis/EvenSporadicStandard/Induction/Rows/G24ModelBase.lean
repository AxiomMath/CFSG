module

public section

namespace CFSG.EvenSporadicStandard.G24Model

@[expose] def parseNums (s : String) : Array Nat :=
  ((s.splitOn " ").filterMap fun t => t.trimAscii.toNat?).toArray

@[expose] def tbl : Array Nat := parseNums (include_str "G24ModelTbl.txt")

abbrev nLines : Nat := 1365

@[expose] def lineU (k : Nat) : Nat := tbl.getD (2 * k) 0

@[expose] def lineW (k : Nat) : Nat := tbl.getD (2 * k + 1) 0

@[expose] def genEntry (j a b : Nat) : Nat := tbl.getD (2 * nLines + 196 * j + 14 * a + b) 0

@[expose] def pgNum (j k : Nat) : Nat :=
  tbl.getD (2 * nLines + 16 * 196 + nLines * j + k) 0 % nLines

abbrev wordOffset : Nat := 2 * nLines + 16 * 196 + 16 * nLines

@[expose] def waLen : Nat := tbl.getD wordOffset 0

@[expose] def waWord : List Nat := (tbl.extract (wordOffset + 1) (wordOffset + 1 + waLen)).toList

@[expose] def wbLen : Nat := tbl.getD (wordOffset + 1 + waLen) 0

@[expose] def wbWord : List Nat :=
  (tbl.extract (wordOffset + 2 + waLen) (wordOffset + 2 + waLen + wbLen)).toList

end CFSG.EvenSporadicStandard.G24Model
