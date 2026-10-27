module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Fischer.F4

public section

namespace CFSG.LieType.Multipliers.L34

open CFSG.Fischer

@[expose] def parseWord (s : String) : List (Fin 2 × Bool) :=
  s.toList.filterMap fun c =>
    if c = 'a' then some (0, true) else if c = 'A' then some (0, false)
    else if c = 'b' then some (1, true) else if c = 'B' then some (1, false) else none

@[expose] def wpow (w : List (Fin 2 × Bool)) (k : ℕ) : List (Fin 2 × Bool) :=
  (List.replicate k w).flatten

theorem mk_wpow (w : List (Fin 2 × Bool)) (k : ℕ) :
    FreeGroup.mk (wpow w k) = FreeGroup.mk w ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wpow, List.replicate_succ', List.flatten_append, ← FreeGroup.mul_mk, ← wpow, ih,
      List.flatten_singleton, pow_succ]

@[expose] def rels : List (List (Fin 2 × Bool)) :=
  ["aa", "bbbbb", "ababababababab", "abaBabaBabaBabaB", "abbABBabbABBabbABB",
    "abbabbabbabbabbabbabb", "ababbaBababbaBababbaBababbaBababbaBababbaBababbaB"].map parseWord

@[expose] def coverPairs : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))
  | 0 => [(parseWord "bab", parseWord "aBaBa"), (parseWord "B", parseWord "BBa")]
  | 1 => [(parseWord "BB", parseWord "abababbababa")]

@[expose] def zOne : List (Fin 2 × Bool) := parseWord "aaabbabbabbabbabbabbabb"

@[expose] def zTwo : List (Fin 2 × Bool) :=
  parseWord "aaababbaBababbaBababbaBababbaBababbaBababbaBababbaB"

@[expose] def zThree : List (Fin 2 × Bool) := parseWord "aaaa"

@[expose] def bFive : List (Fin 2 × Bool) := parseWord "bbbbb"

@[expose] def extraWs : List (List (Fin 2 × Bool)) :=
  [bFive, wpow zOne 4, wpow zTwo 4, wpow zThree 3]

@[expose] def coverWs : List (List (Fin 2 × Bool)) :=
  coverWords rels (fun i => commWords (coverPairs i)) ++ extraWs

@[expose] def walkWords : List (List (Fin 2 × Bool) × ℕ) :=
  [(wpow zOne 2, 2), (wpow zTwo 2, 2), (wpow zOne 2 ++ wpow zTwo 2, 2), (zThree, 3)]

@[expose] def transWords : List String :=
  ["", "", "", "", "", "BBababbaBBaBAbb", "ababbabaBababbaBA", "abbababaBAbAb", "",
    "BabbababaBAbAbb", "bbababbaBBaBABB", "abaBBaBababbABA", "", "", "", "", "",
    "aBBababaBBaBabAb", "ababaBBababaBBabABAB", "abbabbabaBaBBABBA", "", "", "", "", "",
    "aBabaBBabbaBAbA", "aBabababaBABAB", "aBabaBBaBBabaBaBAB", "", "", "", "", "",
    "ababaBBabAbAbb", "ababaBBababaBaBabaBAB", "babaBAbABB", "", "aBababaBaBAbA",
    "ababaBBababaBBAB", "aBabaBBabbababaBBaBB"]

@[expose] def diagWords : List String :=
  ["", "", "", "", "", "", "abaBBababbaBB", "bbaBBaBabbABA", "", "bbaBBaBabbaBa", "AA",
    "abaBBababbABB", "", "abaBBabAbbABB", "bbaBBaBabbaBA", "aa"]

@[expose] def transWord (i j : Fin 3) (c : F4) : List (Fin 2 × Bool) :=
  parseWord (transWords.getD (16 * i.val + 4 * j.val + c.code.val) "")

@[expose] def diagWord (d₀ d₁ : F4) : List (Fin 2 × Bool) :=
  parseWord (diagWords.getD (4 * d₀.code.val + d₁.code.val) "")

structure Mat3 where
  e00 : F4
  e01 : F4
  e02 : F4
  e10 : F4
  e11 : F4
  e12 : F4
  e20 : F4
  e21 : F4
  e22 : F4
deriving DecidableEq

namespace Mat3

@[expose] def mul (x y : Mat3) : Mat3 :=
  ⟨x.e00 * y.e00 + x.e01 * y.e10 + x.e02 * y.e20, x.e00 * y.e01 + x.e01 * y.e11 + x.e02 * y.e21,
    x.e00 * y.e02 + x.e01 * y.e12 + x.e02 * y.e22,
    x.e10 * y.e00 + x.e11 * y.e10 + x.e12 * y.e20, x.e10 * y.e01 + x.e11 * y.e11 + x.e12 * y.e21,
    x.e10 * y.e02 + x.e11 * y.e12 + x.e12 * y.e22,
    x.e20 * y.e00 + x.e21 * y.e10 + x.e22 * y.e20, x.e20 * y.e01 + x.e21 * y.e11 + x.e22 * y.e21,
    x.e20 * y.e02 + x.e21 * y.e12 + x.e22 * y.e22⟩

@[expose] def scalar (c : F4) : Mat3 := ⟨c, 0, 0, 0, c, 0, 0, 0, c⟩

@[expose] def one : Mat3 := scalar 1

@[expose] def ofFun (f : Fin 3 → Fin 3 → F4) : Mat3 :=
  ⟨f 0 0, f 0 1, f 0 2, f 1 0, f 1 1, f 1 2, f 2 0, f 2 1, f 2 2⟩

@[expose] def det (x : Mat3) : F4 :=
  x.e00 * x.e11 * x.e22 - x.e00 * x.e12 * x.e21 - x.e01 * x.e10 * x.e22 +
    x.e01 * x.e12 * x.e20 + x.e02 * x.e10 * x.e21 - x.e02 * x.e11 * x.e20

@[expose] def isScalar (x : Mat3) : Bool := decide (x = scalar x.e00)

end Mat3

@[expose] def aMat : Mat3 := ⟨⟨3⟩, ⟨2⟩, ⟨3⟩, ⟨3⟩, ⟨3⟩, ⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨2⟩⟩

@[expose] def aInvMat : Mat3 := ⟨⟨1⟩, ⟨3⟩, ⟨1⟩, ⟨1⟩, ⟨1⟩, ⟨3⟩, ⟨0⟩, ⟨0⟩, ⟨3⟩⟩

@[expose] def bMat : Mat3 := ⟨⟨1⟩, ⟨2⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨2⟩, ⟨0⟩, ⟨3⟩, ⟨2⟩⟩

@[expose] def bInvMat : Mat3 := ⟨⟨1⟩, ⟨3⟩, ⟨3⟩, ⟨0⟩, ⟨2⟩, ⟨2⟩, ⟨0⟩, ⟨3⟩, ⟨0⟩⟩

@[expose] def letterMat : Fin 2 × Bool → Mat3
  | (0, true) => aMat
  | (0, false) => aInvMat
  | (1, true) => bMat
  | (1, false) => bInvMat

@[expose] def wordMat (w : List (Fin 2 × Bool)) : Mat3 :=
  w.foldr (fun l M => (letterMat l).mul M) Mat3.one

@[expose] def transMat (i j : Fin 3) (c : F4) : Mat3 :=
  Mat3.ofFun fun k l => if k = l then 1 else if k = i ∧ l = j then c else 0

@[expose] def diagMat (d₀ d₁ d₂ : F4) : Mat3 := ⟨d₀, 0, 0, 0, d₁, 0, 0, 0, d₂⟩

end CFSG.LieType.Multipliers.L34
