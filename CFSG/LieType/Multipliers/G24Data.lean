module

public import CFSG.Quasithin.Background.G2UColumns
public import CFSG.Fischer.F4
public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Sporadic.Presentation.SuzInputs

public section

namespace CFSG.LieType.Multipliers.G24

open CFSG.Fischer CFSG.Quasithin.G2U CFSG.Blueprint.Chevalley

section Arrays

variable {R : Type*} [Semiring R]

@[expose] def toMat (n : ℕ) (A : Array (Array R)) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (A.getD i #[]).getD j 0

@[expose] def ofMat {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : Array (Array R) :=
  ((List.finRange n).map fun i => ((List.finRange n).map fun j => M i j).toArray).toArray

@[expose] def mulArr (n : ℕ) (A B : Array (Array R)) : Array (Array R) :=
  ((List.finRange n).map fun i : Fin n => ((List.finRange n).map fun k : Fin n =>
    ∑ j : Fin n, (A.getD i #[]).getD j 0 * (B.getD j #[]).getD k 0).toArray).toArray

theorem getD_finRange_map {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    ((List.finRange n).map f).toArray.getD i d = f i := by
  simp [Array.getD]

theorem toMat_ofMat {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : toMat n (ofMat M) = M := by
  ext i j
  rw [toMat, ofMat, Matrix.of_apply, getD_finRange_map, getD_finRange_map]

theorem toMat_mulArr (n : ℕ) (A B : Array (Array R)) :
    toMat n (mulArr n A B) = toMat n A * toMat n B := by
  ext i k
  rw [toMat, mulArr, Matrix.of_apply, getD_finRange_map, getD_finRange_map, Matrix.mul_apply]
  rfl

end Arrays

@[expose] def letterIdx (c : Char) : Option (Fin 6) :=
  if c = 'a' ∨ c = 'A' then some 0 else if c = 'b' ∨ c = 'B' then some 1
  else if c = 'c' ∨ c = 'C' then some 2 else if c = 'd' ∨ c = 'D' then some 3
  else if c = 'e' ∨ c = 'E' then some 4 else if c = 'g' ∨ c = 'G' then some 5 else none

@[expose] def parseWord (s : String) : List (Fin 6 × Bool) :=
  s.toList.filterMap fun c => (letterIdx c).map fun i => (i, c.isLower)

@[expose] def relStrings : List String :=
  ["aa", "bb", "cc", "dd", "ee", "gg", "ababababab", "bcbcbc", "cdcdcdcdcdcdcdcd", "dedede",
    "gbgbgb", "acac", "adad", "aeae", "agag", "bdbd", "bebe", "cece", "cgcg", "dgdg", "egeg",
    "Acdcdcdcd",
    "bcdcdbcdcdbcdcdbcdcdbcdcdebcdcdbcdcdbcdcdbcdcdbcdcdebcdcdbcdcdbcdcdbcdcdbcdcde",
    "abcgabcgabcgabcgabcg"]

@[expose] def rels : List (List (Fin 6 × Bool)) := relStrings.map parseWord

@[expose] def dSq : List (Fin 6 × Bool) := parseWord "dd"

@[expose] def pairStrings : List (List (String × String)) :=
  [[("c", "d"), ("c", "d")],
    [("a", "b"), ("d", "abcdc")],
    [("a", "b"), ("ac", "bab")],
    [("edcb", "ababdcd"), ("cbde", "acdcba")],
    [("cbde", "cdcbad"), ("edcb", "ababdcd")],
    [("a", "b"), ("ag", "bab")]]

@[expose] def pairs (i : Fin 6) : List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) :=
  (pairStrings.getD i []).map fun p => (parseWord p.1, parseWord p.2)

@[expose] def genStringsX : List String :=
  ["", "a", "ag", "g", "", "dcbabcedgbabcdcbabgedcbabgd", "acdedcbadcbagbcdcbgedbca",
    "adedcbdcgbcdcedcabgcdbcdecd"]

@[expose] def genStringsY : List String :=
  ["", "bcbgbcdcbabedcgdebabcdcbgbcb", "gbacbdcedcbdcgdabcdecdbcabg",
    "bcdgbcdcbedcdegbcdcbgdcb", "", "bdcbabacgbcdcedcbgedabcdbab", "bcedcbagbcdcedcbgbabcdecba",
    "bdcbabacgbcdcedcbgedabcdbabbcedcbagbcdcedcbgbabcdecba"]

@[expose] def genWordX (i : Fin Tag.G2.rank) (c : F4) : List (Fin 6 × Bool) :=
  parseWord (genStringsX.getD (4 * i.val + c.code.val) "")

@[expose] def genWordY (i : Fin Tag.G2.rank) (c : F4) : List (Fin 6 × Bool) :=
  parseWord (genStringsY.getD (4 * i.val + c.code.val) "")

@[expose] def f4Digit (c : Char) : F4 :=
  ⟨⟨(c.toNat - 48) % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def genRows : List (List String) :=
  [["11000000000000", "01000000000000", "00100000000000", "00011000000000", "00001000000000",
    "00000101100000", "00000010100000", "00000001000000", "00000000100000", "00000000011000",
    "00000000001000", "00000000000100", "00000000000011", "00000000000001"],
  ["30313321312203", "22301000200000", "33002202233102", "21120112231302", "22323132023301",
    "02223203302223", "22201312322201", "31002001031002", "11203303211203", "12303321330213",
    "00300000222001", "31133202231033", "31102112221320", "23301132022323"],
  ["11203010002001", "01000000100000", "03100000001000", "02011022003102", "00001000200000",
    "10030100020010", "01000010002000", "01003001002001", "00000000100000", "03102030011003",
    "00000000301000", "00001000000102", "01003011002311", "00000000100001"],
  ["11000000000000", "01000000000000", "00100000000000", "22011000000000", "02001000000000",
    "11000101100000", "01200010100000", "01000001000000", "00000000100000", "33100000011000",
    "03000000001000", "02301002000100", "10233011122011", "01003000102001"],
  ["03001022302311", "00000000200001", "00003000200203", "03101020133002", "00000000203000",
    "20133122221223", "00003011200002", "02003001202002", "00000000100000", "03021033301301",
    "00002000300000", "02300000101000", "13203020003003", "01000000200000"],
  ["13000000000000", "01000000000000", "00100000000000", "00013000000000", "00001000000000",
    "00000103200000", "00000010300000", "00000001000000", "00000000100000", "00000000013000",
    "00000000001000", "00000000000100", "00000000000013", "00000000000001"]]

@[expose] def genArrs : List (Array (Array F4)) :=
  genRows.map fun rs => (rs.map fun s => (s.toList.map f4Digit).toArray).toArray

@[expose] def genArr (i : Fin 6) : Array (Array F4) := genArrs.getD i #[]

@[expose] def one14 : Array (Array F4) := ofMat (1 : Matrix (Fin 14) (Fin 14) F4)

@[expose] def wordArr (w : List (Fin 6 × Bool)) : Array (Array F4) :=
  w.foldr (fun l A => mulArr 14 (genArr l.1) A) one14

@[expose] def allF4 : List F4 := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]

theorem mem_allF4 (c : F4) : c ∈ allF4 := by
  obtain ⟨c⟩ := c
  fin_cases c <;> simp [allF4]

@[expose] def invCheck : Bool :=
  (List.finRange 6).all fun i =>
    decide (mulArr 14 (genArr i) (genArr i) = one14)

@[expose] def relCheck : Bool :=
  rels.all fun r => decide (wordArr r = one14)

@[expose] def commCheck : Bool :=
  (List.finRange 6).all fun i => decide (wordArr (commWords (pairs i)) = genArr i)

@[expose] def rootCheck : Bool :=
  (List.finRange Tag.G2.rank).all fun i => allF4.all fun c =>
    decide (ofMat (XMat F4 i c) = wordArr (genWordX i c)) &&
      decide (ofMat (YMat F4 i c) = wordArr (genWordY i c))

@[expose] def suzCheck : Bool :=
  decide ((CFSG.CosetTable.subsetOf TauCeti.SporadicName.Suz.presentation.generatorCount
      [0, 1, 2, 3, 4, 6]).length = 6) &&
    decide (CFSG.Sporadic.Presentation.Suz.R1.map (List.map fun l => (l.1.val, l.2)) =
      rels.map (List.map fun l => (l.1.val, l.2)))

@[expose] def z3Digit (c : Char) : ZMod 3 := ((c.toNat - 48 : ℕ) : ZMod 3)

@[expose] def liftRows : List (List String) :=
  [["222111120021", "221211112012", "001001101111", "202210102021", "221211010102",
    "001001202222", "101120222102", "121000122102", "010020101210", "100021002020",
    "022211211101", "102022100200"],
  ["100121201221", "020100202000", "021220111020", "011012220000", "222100212201",
    "200120201221", "100010200122", "200220121211", "211202121211", "022221110200",
    "011110222000", "200022001200"],
  ["210211100020", "011101222002", "022220121102", "001100120012", "022010001120",
    "022022001120", "012210022222", "021101212002", "012101222212", "022222110201",
    "020002020102", "001001011100"],
  ["002201010022", "010021021121", "110000010002", "112222222122", "120101202222",
    "112112000120", "212122102011", "020102001010", "000210022200", "021200021220",
    "010001100222", "000021002120"],
  ["110110020022", "012120220020", "202221000022", "200112212022", "110212021222",
    "220020000122", "220200001022", "000220000020", "221010102201", "101112011101",
    "020012110122", "212022000111"],
  ["100220222020", "110012101220", "002000000000", "111202012102", "120002101220",
    "010212212100", "211221222122", "200111010010", "002021010011", "201202211212",
    "022002200221", "220010010222"]]

@[expose] def liftArrs : List (Array (Array (ZMod 3))) :=
  liftRows.map fun rs => (rs.map fun s => (s.toList.map z3Digit).toArray).toArray

@[expose] def liftInvArrs : List (Array (Array (ZMod 3))) :=
  liftArrs.map fun A => mulArr 12 A (mulArr 12 A A)

@[expose] def liftArr (i : Fin 6) : Array (Array (ZMod 3)) := liftArrs.getD i #[]

@[expose] def liftInvArr (i : Fin 6) : Array (Array (ZMod 3)) := liftInvArrs.getD i #[]

@[expose] def one12 : Array (Array (ZMod 3)) := ofMat (1 : Matrix (Fin 12) (Fin 12) (ZMod 3))

@[expose] def letterArr3 (l : Fin 6 × Bool) : Array (Array (ZMod 3)) :=
  if l.2 then liftArr l.1 else liftInvArr l.1

@[expose] def wordArr3 (w : List (Fin 6 × Bool)) : Array (Array (ZMod 3)) :=
  w.foldr (fun l A => mulArr 12 (letterArr3 l) A) one12

@[expose] def unitCheck : Bool :=
  (List.finRange 6).all fun i =>
    decide (mulArr 12 (liftArr i) (liftInvArr i) = one12) &&
      decide (mulArr 12 (liftInvArr i) (liftArr i) = one12)

@[expose] def coverCheck : Bool :=
  (coverWords rels fun i => commWords (pairs i)).all fun r =>
    decide (wordArr3 r = one12)

@[expose] def kerCheck : Bool :=
  !decide (wordArr3 dSq = one12) && decide (mulArr 12 (wordArr3 dSq) (wordArr3 dSq) = one12)

end CFSG.LieType.Multipliers.G24
