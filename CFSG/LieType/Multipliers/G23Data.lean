module

public import CFSG.Quasithin.Background.G2UColumns
public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.LieType.Multipliers.G23

open CFSG.Sporadic.He.Native CFSG.Quasithin.G2U

@[expose] def parseWord (s : String) : List (Fin 2 × Bool) :=
  s.toList.filterMap fun c =>
    if c = 'a' then some (0, true) else if c = 'A' then some (0, false)
    else if c = 'b' then some (1, true) else if c = 'B' then some (1, false) else none

@[expose] def rep (k : ℕ) (s : String) : String := String.join (List.replicate k s)

@[expose] def relSixString : String :=
  rep 2 (rep 2 (rep 3 "ab" ++ "aB") ++ rep 2 "ab" ++ rep 2 "aB")

@[expose] def relStrings : List String :=
  ["aa", "bbb", rep 13 "ab", rep 13 "aBab",
    "abab" ++ rep 4 "aBab" ++ rep 3 "ab" ++ rep 3 "aBaBabab", relSixString]

@[expose] def rels : List (List (Fin 2 × Bool)) := relStrings.map parseWord

@[expose] def relSix : List (Fin 2 × Bool) := parseWord relSixString

@[expose] def genWordStrings : List String :=
  ["abaBaBaBaBaBabababab", "abaBaBabaBabaBaBabaB", "aBaBabaBaBaBabababababaBabababa",
    "aBaBababaBabaBaBabaBabaBabababa"]

@[expose] def genWord (j : Fin 4) : List (Fin 2 × Bool) :=
  parseWord (genWordStrings.getD j.val "")

@[expose] def pairs : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))
  | 0 => [(parseWord "babaBaB", parseWord "ababaBaBa"),
      (parseWord "baB", parseWord "aBabaBabaBa")]
  | 1 => [(parseWord "abaBabaBaba", parseWord "BaB"), (parseWord "bab", parseWord "aBabaBa")]

@[expose] def arrOf (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Array (Array ℕ) :=
  Array.ofFn fun i => Array.ofFn fun j => (M i j).val

@[expose] def rootMat : Fin 4 → Matrix (Fin 14) (Fin 14) (ZMod 3)
  | 0 => XMat (ZMod 3) (ix 0) 1
  | 1 => XMat (ZMod 3) (ix 1) 1
  | 2 => YMat (ZMod 3) (ix 0) 1
  | 3 => YMat (ZMod 3) (ix 1) 1

@[expose] def rootArr (j : Fin 4) : Array (Array ℕ) := arrOf (rootMat j)

@[expose] def rootProd (js : List (Fin 4)) : Array (Array ℕ) :=
  js.foldr (fun j M => mulM 3 14 (rootArr j) M) (idM 14)

@[expose] def aWord : List (Fin 4) := [0, 1, 2, 0, 2]

@[expose] def bWord : List (Fin 4) := [3, 1, 2, 3, 3]

@[expose] def aArr : Array (Array ℕ) := rootProd aWord

@[expose] def bArr : Array (Array ℕ) := rootProd bWord

@[expose] def bInvArr : Array (Array ℕ) := mulM 3 14 bArr bArr

@[expose] def letterArr : Fin 2 × Bool → Array (Array ℕ)
  | (0, _) => aArr
  | (1, true) => bArr
  | (1, false) => bInvArr

@[expose] def wordArr (w : List (Fin 2 × Bool)) : Array (Array ℕ) :=
  w.foldr (fun l M => mulM 3 14 (letterArr l) M) (idM 14)

@[expose] def modelCheck : Bool :=
  (mulM 3 14 aArr aArr == idM 14) && (mulM 3 14 bArr bInvArr == idM 14) &&
    rels.all (fun r => wordArr r == idM 14) &&
    (List.finRange 4).all (fun j => wordArr (genWord j) == rootArr j) &&
    (List.finRange 2).all fun i => wordArr (commWords (pairs i)) == letterArr (i, true)

@[expose] def atlasA : String :=
  "1     4    27    27\n\
  133232212200322231332202222 130121132010211020321331333 001020002311130113112032030 \
  020202022333003030311022220 122323101021110302002323223 033332133220322012223321131 \
  033022323323323032323103130 122332300001013223310323310 312003303232112302101233021 \
  122002110202201332130021222 322132100030122212010330121 320313312002211131020333332 \
  001120222132333230220020132 023330030221022210301221332 211230111302021112213111222 \
  200133322212233321330200221 023102010331031033102120301 302333212231023001200103002 \
  312023303103001222122031203 022102203120012223320232110 023111232011113002231223002 \
  131223323331222023303021221 233323023232301123000311223 313111010221331032110110112 \
  320213231010010103303030102 110220001110123101033313333 223320212310013031323033133"

@[expose] def atlasB : String :=
  "1     4    27    27\n\
  210033222030311223203031223 131322001100312331211121310 213030130303121112230333302 \
  221201202223330301023323333 210233132101211221303233111 322120131211131333000221112 \
  021020202021130302113013113 313232212322133133110013120 120320121310212011032113110 \
  311133302210331223321030013 010021322100211302233032100 301113012110020212311023221 \
  213301301023312123101123212 322020111123233210202103332 202113321323212222102312102 \
  021013002103022332310130111 021023120020203101132133032 231123002023133002022310033 \
  210300113312030332210013210 300120121220220223123003201 130122011120132333003232000 \
  130130031010203030231122031 031223301001010301200031112 013003033123113100131301322 \
  300121330103102031232210310 223330201003112110111330020 322012102310312312213002311"

@[expose] def blockEntry (c k l : ℕ) : ℕ :=
  if k = 0 then (if l = 0 then c % 2 else c / 2 % 2)
  else if l = 0 then c / 2 % 2 else (c % 2 + c / 2 % 2) % 2

@[expose] def blowUp (M : Array (Array ℕ)) : Array (Array ℕ) :=
  Array.ofFn (n := 54) fun r => Array.ofFn (n := 54) fun c =>
    blockEntry (M[r.val / 2]!)[c.val / 2]! (r.val % 2) (c.val % 2)

@[expose] def coverA : Array (Array ℕ) := blowUp (rowsOf 4 27 atlasA)

@[expose] def coverB : Array (Array ℕ) := blowUp (rowsOf 4 27 atlasB)

@[expose] def coverBInv : Array (Array ℕ) := mulM 2 54 coverB coverB

@[expose] def coverLetter : Fin 2 × Bool → Array (Array ℕ)
  | (0, _) => coverA
  | (1, true) => coverB
  | (1, false) => coverBInv

@[expose] def coverWordArr (w : List (Fin 2 × Bool)) : Array (Array ℕ) :=
  w.foldr (fun l M => mulM 2 54 (coverLetter l) M) (idM 54)

@[expose] def coverCheck : Bool :=
  (mulM 2 54 coverA coverA == idM 54) && (mulM 2 54 coverB coverBInv == idM 54) &&
    (coverWords rels fun i => commWords (pairs i)).all fun v => coverWordArr v == idM 54

@[expose] def relSixCheck : Bool :=
  (mulM 2 54 (coverWordArr relSix) (mulM 2 54 (coverWordArr relSix) (coverWordArr relSix)) ==
      idM 54) && ((coverWordArr relSix)[0]!)[1]! == 1

end CFSG.LieType.Multipliers.G23
