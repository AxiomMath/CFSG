module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversCycle
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.M23Gens

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Covers
open CFSG.Sporadic.Schreier CFSG.Blueprint TauCeti
open scoped Pointwise

abbrev M23g : Type := NativeSporadic.M23

@[expose] def gM : Fin 2 → M23g := ![m23GenA, m23GenB⁻¹]

@[expose] def m23R1 : List Letter :=
  [(0, true), (0, true)]

@[expose] def m23R2 : List Letter :=
  [(1, true), (1, true), (1, true), (1, true)]

@[expose] def m23R3 : List Letter :=
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)]

@[expose] def m23R4 : List Letter :=
  [(0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
    (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true),
    (1, true), (1, true)]

@[expose] def m23R5 : List Letter :=
  [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true),
    (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true),
    (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)]

@[expose] def m23R6 : List Letter :=
  [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true),
    (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (1, true)]

@[expose] def m23R7 : List Letter :=
  [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)]

@[expose] def m23R8 : List Letter :=
  [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true)]

@[expose] def m23R9 : List Letter :=
  [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
    (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
    (0, true), (1, false), (0, true), (1, true), (1, true)]

@[expose] def m23R : List (List Letter) :=
  [m23R1, m23R2, m23R3, m23R4, m23R5, m23R6, m23R7, m23R8, m23R9]

@[expose] def m23Rw (i : Fin 9) : List Letter := m23R.getD i []

@[expose] def alphaW : List Letter :=
  [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, false), (0, true), (1, false)]

@[expose] def betaW : List Letter :=
  [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
    (0, true), (1, true)]

@[expose] def D23 : Finset (Fin 23) := {0, 1, 2, 3, 4, 13, 15, 16, 17, 19, 21, 22}

@[expose] def alphaG : M23g := wordVal gM alphaW

@[expose] def betaG : M23g := wordVal gM betaW

@[expose] def yM : Fin 2 → M23g := ![alphaG, betaG]

@[expose] def vstep (S : Finset (Finset (Fin 23))) : Finset (Finset (Fin 23)) :=
  S ∪ S.image (fun s => gM 0 • s) ∪ S.image (fun s => gM 1 • s)

@[expose] def bfs (n : ℕ) : Finset (Finset (Fin 23)) := vstep^[n] {D23}

@[expose] def cycCells : Fin 7 → List (Finset (Fin 23) × Fin 9)
  | 0 => [(({0, 2, 3, 5, 7, 10, 11, 12, 13, 14, 21, 22} : Finset (Fin 23)), 5)]
  | 1 => [(({1, 4, 7, 10, 12, 14, 15, 16, 18, 20, 21, 22} : Finset (Fin 23)), 4)]
  | 2 => [(({0, 2, 3, 5, 6, 7, 8, 12, 14, 15, 16, 21} : Finset (Fin 23)), 3)]
  | 3 => [(({2, 3, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17} : Finset (Fin 23)), 0)]
  | 4 => [(({1, 2, 3, 5, 6, 7, 9, 13, 14, 15, 16, 20} : Finset (Fin 23)), 1)]
  | 5 => [(({0, 4, 9, 10, 11, 12, 14, 15, 16, 18, 19, 21} : Finset (Fin 23)), 7)]
  | 6 => [(({0, 1, 2, 3, 4, 13, 15, 16, 17, 19, 21, 22} : Finset (Fin 23)), 3),
    (({0, 1, 2, 3, 4, 12, 14, 16, 17, 18, 20, 22} : Finset (Fin 23)), 3),
    (({2, 3, 7, 8, 10, 11, 13, 14, 16, 18, 19, 22} : Finset (Fin 23)), 0),
    (({1, 2, 3, 5, 6, 10, 11, 12, 13, 15, 20, 22} : Finset (Fin 23)), 8),
    (({0, 6, 7, 8, 10, 11, 15, 17, 19, 20, 21, 22} : Finset (Fin 23)), 4),
    (({3, 4, 5, 6, 10, 14, 16, 17, 18, 20, 21, 22} : Finset (Fin 23)), 1),
    (({1, 6, 7, 9, 10, 11, 14, 17, 18, 20, 21, 22} : Finset (Fin 23)), 1),
    (({3, 5, 6, 7, 8, 13, 14, 15, 16, 17, 18, 22} : Finset (Fin 23)), 3),
    (({2, 3, 4, 5, 6, 7, 11, 13, 14, 16, 18, 21} : Finset (Fin 23)), 0),
    (({0, 2, 3, 5, 6, 7, 8, 12, 14, 15, 16, 21} : Finset (Fin 23)), 0),
    (({0, 2, 3, 5, 6, 7, 8, 12, 14, 15, 16, 21} : Finset (Fin 23)), 7),
    (({2, 3, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17} : Finset (Fin 23)), 7),
    (({0, 1, 6, 7, 8, 9, 10, 13, 15, 16, 19, 20} : Finset (Fin 23)), 1),
    (({0, 1, 6, 7, 8, 9, 10, 13, 15, 16, 19, 20} : Finset (Fin 23)), 5),
    (({0, 1, 2, 4, 5, 7, 8, 9, 11, 15, 18, 22} : Finset (Fin 23)), 5),
    (({0, 1, 2, 4, 5, 7, 8, 9, 11, 15, 18, 22} : Finset (Fin 23)), 8),
    (({2, 3, 4, 5, 6, 7, 11, 12, 15, 16, 19, 20} : Finset (Fin 23)), 1),
    (({0, 1, 4, 5, 6, 7, 11, 12, 15, 16, 18, 21} : Finset (Fin 23)), 0),
    (({0, 1, 4, 5, 6, 7, 11, 12, 15, 16, 18, 21} : Finset (Fin 23)), 6),
    (({0, 1, 2, 4, 6, 8, 9, 11, 12, 14, 15, 21} : Finset (Fin 23)), 4),
    (({4, 6, 7, 8, 9, 13, 15, 16, 17, 19, 21, 22} : Finset (Fin 23)), 0),
    (({1, 6, 7, 9, 12, 13, 14, 16, 19, 20, 21, 22} : Finset (Fin 23)), 0),
    (({1, 3, 4, 6, 7, 8, 9, 12, 15, 16, 20, 21} : Finset (Fin 23)), 0),
    (({1, 2, 3, 6, 7, 8, 12, 13, 15, 16, 19, 22} : Finset (Fin 23)), 0),
    (({1, 3, 4, 7, 9, 10, 11, 12, 13, 20, 21, 22} : Finset (Fin 23)), 6),
    (({0, 2, 4, 7, 8, 11, 13, 15, 16, 19, 20, 22} : Finset (Fin 23)), 8),
    (({0, 1, 2, 3, 4, 8, 9, 11, 16, 20, 21, 22} : Finset (Fin 23)), 6),
    (({0, 2, 3, 6, 7, 9, 12, 13, 14, 16, 18, 22} : Finset (Fin 23)), 1),
    (({3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 16, 18} : Finset (Fin 23)), 0)]

@[expose] def cycWords (k : Fin 7) : List (Finset (Fin 23) × List Letter) :=
  (cycCells k).map fun p => (p.1, m23Rw p.2)

@[expose] def cycKeys (k : Fin 7) : List (Finset (Fin 23) × Fin 2) :=
  (cycWords k).flatMap fun c => wordKeys gM c.2 c.1

@[expose] def cellsIn (B : Finset (Finset (Fin 23))) : Bool :=
  (List.finRange 7).all fun k => (cycCells k).all fun p => decide (p.1 ∈ B)

@[expose] def allEven (L : List (Finset (Fin 23) × Fin 2)) : Bool :=
  L.all fun e => decide (Even (L.count e))

@[expose] def orbitCheck : Bool :=
  let B := bfs 22
  decide (B.card = 1288) && cellsIn B

end CFSG.QuasithinUnique.Vol2Native.L239.Covers
