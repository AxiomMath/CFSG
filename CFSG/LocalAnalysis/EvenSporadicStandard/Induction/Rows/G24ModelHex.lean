module

public import CFSG.Fischer.F4
public import CFSG.Quasithin.Background.G2UColumns
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelBase

public section

namespace CFSG.EvenSporadicStandard.G24Model

open CFSG.Fischer CFSG.Quasithin.G2U CFSG.Blueprint.Chevalley

abbrev Vec : Type := Fin 14 → F4

@[expose] def f4 (c : Nat) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def decodeVec (n : Nat) : Vec := fun i => f4 (n / 4 ^ (i : Nat))

@[expose] def comb (c d : Nat) (u w : Vec) : Vec := fun i => f4 c * u i + f4 d * w i

@[expose] def uVec (k : Nat) : Vec := decodeVec (lineU k)

@[expose] def wVec (k : Nat) : Vec := decodeVec (lineW k)

@[expose] def lineVecs (k : Nat) : List Vec :=
  (List.range 4).flatMap fun c => (List.range 4).filterMap fun d =>
    if c = 0 ∧ d = 0 then none else some (comb c d (uVec k) (wVec k))

@[expose] def lineOf (k : Fin nLines) : Finset Vec := (lineVecs k).toFinset

@[expose] def Gmat (j : Fin 16) : Matrix (Fin 14) (Fin 14) F4 :=
  Matrix.of fun a b => f4 (genEntry j a b)

@[expose] def pgFin (j : Fin 16) (k : Fin nLines) : Fin nLines :=
  ⟨pgNum j k, Nat.mod_lt _ (by norm_num)⟩

@[expose] def vecCode (v : Vec) : Nat := ∑ i : Fin 14, (v i).code.val * 4 ^ (i : Nat)

@[expose] def keyOfSet (s : Finset Vec) : List Nat := (s.image vecCode).sort (· ≤ ·)

@[expose] def lineKeys : Array (List Nat) := Array.ofFn fun k : Fin nLines => keyOfSet (lineOf k)

@[expose] def vecList (v : Vec) : List F4 := (List.finRange 14).map v

@[expose] def lineLists : Array (List (List F4)) :=
  Array.ofFn fun k : Fin nLines => (lineVecs k).map vecList

@[expose] def imgIn (M : Matrix (Fin 14) (Fin 14) F4) (v : Vec) (L : List (List F4)) : Bool :=
  decide (vecList (M.mulVec v) ∈ L)

@[expose] def hexOK : Bool :=
  decide ((∀ k : Fin nLines, (lineOf k).card = 15 ∧ (0 : Vec) ∉ lineVecs k) ∧
      ∀ k k' : Fin nLines, k ≠ k' → lineKeys[(k : Nat)]! ≠ lineKeys[(k' : Nat)]!) &&
    (List.finRange 16).all fun j => (List.finRange nLines).all fun k =>
      imgIn (Gmat j) (uVec k) lineLists[(pgFin j k : Nat)]! &&
        imgIn (Gmat j) (wVec k) lineLists[(pgFin j k : Nat)]!

@[expose] def xIdx (i : Fin 2) (c : F4) : Fin 16 :=
  ⟨4 * (i : Nat) + (c.code : Nat), by
    have h1 : (i : Nat) < 2 := i.2
    have h2 : (c.code : Nat) < 4 := c.code.2
    omega⟩

@[expose] def yIdx (i : Fin 2) (c : F4) : Fin 16 :=
  ⟨8 + 4 * (i : Nat) + (c.code : Nat), by
    have h1 : (i : Nat) < 2 := i.2
    have h2 : (c.code : Nat) < 4 := c.code.2
    omega⟩

@[expose] def xEnt (i : Fin 2) (c : F4) (a b : Fin 14) : F4 := XMat F4 i c a b

@[expose] def yEnt (i : Fin 2) (c : F4) (a b : Fin 14) : F4 := YMat F4 i c a b

@[expose] def gEnt (j : Fin 16) (a b : Fin 14) : F4 := Gmat j a b

@[expose] def genOK : Bool :=
  decide ((∀ (i : Fin 2) (c : F4) (a b : Fin 14), xEnt i c a b = gEnt (xIdx i c) a b) ∧
    ∀ (i : Fin 2) (c : F4) (a b : Fin 14), yEnt i c a b = gEnt (yIdx i c) a b)

end CFSG.EvenSporadicStandard.G24Model
