module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Act
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelU43Arr
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.EvenSmallLie.Child3.SelL39

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.LieType.Multipliers.U43
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

@[expose] def mv3 (A : Matrix (Fin 3) (Fin 3) F9) (v : V3) : V3 :=
  fun i => A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2

@[expose] def MA : Matrix (Fin 3) (Fin 3) F9 :=
  !![⟨1, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩;
    ⟨0, 1⟩, ⟨2, 0⟩, ⟨2, 0⟩;
    ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]

@[expose] def MB : Matrix (Fin 3) (Fin 3) F9 :=
  !![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨2, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]

@[expose] def NA : Matrix (Fin 3) (Fin 3) F9 :=
  !![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 2⟩;
    ⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩;
    ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩]

@[expose] def NB : Matrix (Fin 3) (Fin 3) F9 :=
  !![⟨1, 0⟩, ⟨0, 2⟩, ⟨1, 0⟩;
    ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]

@[expose] def ptArr (M : Matrix (Fin 3) (Fin 3) F9) : Array ℕ :=
  Array.ofFn (n := 91) fun i => ptIndex3 (mv3 M (decode3 i.val))

@[expose] def pA : Array ℕ := ptArr MA

@[expose] def pB : Array ℕ := ptArr MB

@[expose] def lA : Array ℕ := ptArr NA

@[expose] def lB : Array ℕ := ptArr NB

@[expose] def blockArr (p l : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 182) fun i => if i.val < 91 then p[i.val]! else 91 + l[i.val - 91]!

@[expose] def qA : Array ℕ := blockArr pA lA

@[expose] def qB : Array ℕ := blockArr pB lB

@[expose] def frob3 (v : V3) : V3 := fun k => v k * v k * v k

@[expose] def sig182 : Array ℕ :=
  Array.ofFn (n := 182) fun i =>
    if i.val < 91 then ptIndex3 (frob3 (decode3 i.val))
    else 91 + ptIndex3 (frob3 (decode3 (i.val - 91)))

@[expose] def gam182 : Array ℕ := Array.ofFn (n := 182) fun i => (i.val + 91) % 182

@[expose] def tWords : List (List ℤ) :=
    [[-1, -2, -2, 1, 1], [3, 3, 3, 3, 1, 3, 1, -2], [-4, -4, -4, -4, -4, -4, -4, -4],
     [4, 3, -5, 3, 5, 3], [6, 5, 6, 6, -4, -3, -6, -3, 4, 6, 3]]

@[expose] def t1S : Array (Array ℕ) := pushWords 91 #[pA, pB] tWords

@[expose] def t1Base : List (Fin 91) := [0, 1, 2, 9, 10]

@[expose] def tS : Array (Array ℕ) := pushWords 182 #[qA, qB] tWords

@[expose] def tBase : List (Fin 182) := [0, 1, 2, 9, 10]

@[expose] def autGens : Array (Array ℕ) := #[qA, qB, sig182, gam182]

@[expose] def autWords : List (List ℤ) :=
    [[-1, -3, 2, -1], [-5, -5], [-3, 6, 3], [-5, 7, 5], [-3, 8, 3],
     [-6, -8, -9, 7, -5, -3, -5, 3, 5, 3], [-1, -5, 6, 1], [6, 7, 8, 9, -11, 3, 11],
     [-11, -10, -6, 11], [-11, -10, 11, 6, 11], [-6, -7, -10, 14, -3, -11, -10, -1, -2, 14, 1]]

@[expose] def autS : Array (Array ℕ) := pushWords 182 autGens autWords

@[expose] def autBase : List (Fin 182) := [0, 1, 2, 9, 10, 3]

@[expose] def autW (w : List ℤ) : Array ℕ := wordA 182 autS (rawInvs 182 autS) w

@[expose] def sylowGenWords : List (List ℤ) :=
    [[-7, 11, 14, 12, 8, 6, 10, 12], [13, 1, -7, 15, 11, -14, -15, -9, 7, 15, 10, 12],
     [9, 2, 1, -10, 11, 3, 14, 13, -6, 8, -15, 12],
     [2, 4, 1, 9, 6, 11, -13, 9, -15, -6, 10, 10]]

@[expose] def sylowGens : Array (Array ℕ) := (sylowGenWords.map autW).toArray

@[expose] def sylowWords : List (List ℤ) :=
    [[-1, -2, -2, 1], [-1, -4, -4, 1], [-1, -2, 6, 1], [-1, -7, -3, 1]]

@[expose] def sylowS : Array (Array ℕ) := pushWords 182 sylowGens sylowWords

@[expose] def sylowBase : List (Fin 182) := [1, 0]

@[expose] def tChainCheck : Bool :=
  rawChainOK 91 (t1S.extract 0 2) t1S (t1Base.map Fin.val).toArray (wordsOf 2 tWords) 4 &&
    rawOrbitSizes 91 t1S (t1Base.map Fin.val).toArray == [91, 90, 8, 81, 8] &&
    rawChainOK 182 (tS.extract 0 2) tS (tBase.map Fin.val).toArray (wordsOf 2 tWords) 4 &&
    rawOrbitSizes 182 tS (tBase.map Fin.val).toArray == [91, 90, 8, 81, 8] &&
    isInvA 91 lA (invCand 91 lA) && isInvA 91 lB (invCand 91 lB)

@[expose] def autChainCheck : Bool :=
  rawChainOK 182 (autS.extract 0 4) autS (autBase.map Fin.val).toArray (wordsOf 4 autWords) 4 &&
    rawOrbitSizes 182 autS (autBase.map Fin.val).toArray == [182, 90, 8, 81, 8, 2]

@[expose] def sylowChainCheck : Bool :=
  sylowGenWords.all (lettersOK autS.size) &&
    rawChainOK 182 (sylowS.extract 0 4) sylowS (sylowBase.map Fin.val).toArray
      (wordsOf 4 sylowWords) 4 &&
    rawOrbitSizes 182 sylowS (sylowBase.map Fin.val).toArray == [32, 16]

@[expose] def normCheck : Bool :=
  [sig182, gam182].all fun g => isInvA 182 g (invCand 182 g) &&
    [qA, qB].all fun x =>
      siftA 182 (rawLevels 182 tS (tBase.map Fin.val).toArray) (tBase.map Fin.val).toArray 0
        (conjA 182 g x)

@[expose] def l39Roots : List (ℕ × List (List ℤ)) :=
    [(0, [[3], [4], [5], [6], [7]]),
     (91, [[-1, -2, 6, -3, 6], [-6, 3, 2, -1, 2]])]

@[expose] def centCheck : Bool := centOK 182 tS l39Roots

@[expose] def sylowW (w : List ℤ) : Array ℕ := wordA 182 sylowS (rawInvs 182 sylowS) w

@[expose] def tW (w : List ℤ) : Array ℕ := wordA 182 tS (rawInvs 182 tS) w

@[expose] def sylowTables : List (List Table) :=
  chainTables 182 sylowS (sylowBase.map Fin.val).toArray

@[expose] def sylowGensT : Array Table := sylowGens.map (arrTable 182)

@[expose] def sylowGensInvT : Array Table := sylowGens.map fun t => arrTable 182 (invCand 182 t)

@[expose] def invList : List Table := filterProducts 182 (ordTest 182 2) sylowTables (idT 182) []

@[expose] def repWords : List (List ℤ) :=
    [[1], [2, 2], [4, 2], [3, 1, 7], [-4, 2, 8, 7], [2, 2, 6, 8], [-4, -7], [2, 2, 5],
     [4, 2, 1, 5], [4, 3, 1, 6], [2, 4, 8, 5]]

@[expose] def repArrs : List (Array ℕ) := repWords.map sylowW

@[expose] def witWords : List (List ℤ) :=
    [[-4, 1, 4, 4, 4, 6, 6, 7], [-1, 2, -4, 3, 4, 6, -5, 6, 7, 7],
     [6, 1, -6, -4, 3, 4, 4, 4, 4, 5, 6, -5, -7], [4, 2, -1, 7, 3, 4, 4, 4, 6, 5, 6, -7, -7],
     [7, 5, 1, -6, -4, 3, -4, -4, -4, 7, -5, 6, 5, -7, -7, -7],
     [6, 2, -6, -4, 3, 4, 4, 7, 5, 6, 7, 7], [-7, 2, 1, -3, -7, 3, -4, -4, -5, -6, 5, 7, 7],
     [1, 6, 1, 3, -5, 3, 3, -4, -4, -7, 5, 7, 7, 7],
     [1, 2, -3, -3, -4, -4, -4, -7, 6, 6, 5, 7, 7, 7, 7],
     [6, 2, -3, -6, 5, 3, 4, 4, -6, 5, -6], [2, 3, 1, -3, -6, 3, -4, -4, 6, -5, 6, 7, 7, 7, 7]]

@[expose] def repsCheck : Bool :=
  repsOK 182 sylowGensT sylowGensInvT invList (repArrs.map (arrTable 182)) 100 &&
    repArrs.all fun r => ordTest 182 2 (arrTable 182 r)

@[expose] def witCheck : Bool :=
  repWords.all (lettersOK sylowS.size) && witWords.all (lettersOK tS.size) &&
    repWords.length == 11 && witWords.length == 11 &&
    (List.range 11).all fun j => witOK 182 (repArrs.getD j #[]) (tW (witWords.getD j []))

end CFSG.EvenSmallLie.Child3.SelL39
