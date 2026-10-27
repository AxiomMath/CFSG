module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
open Equiv

@[expose] def mkPerm6 (f g : Fin 6 → Fin 6) (h₁ : ∀ i, g (f i) = i := by decide)
    (h₂ : ∀ i, f (g i) = i := by decide) : Perm (Fin 6) :=
  ⟨f, g, h₁, h₂⟩

@[expose] def blockPerm0 : Perm (Fin 6) := mkPerm6 ![5, 3, 0, 2, 4, 1] ![2, 5, 3, 1, 4, 0]

@[expose] def blockPerm1 : Perm (Fin 6) := mkPerm6 ![2, 5, 0, 4, 3, 1] ![2, 5, 0, 4, 3, 1]

@[expose] def blockTau2 : Perm (Fin 6) := mkPerm6 ![4, 5, 3, 2, 0, 1] ![4, 5, 3, 2, 0, 1]

@[expose] def blockTau3 : Perm (Fin 6) := mkPerm6 ![0, 2, 3, 5, 4, 1] ![0, 5, 1, 2, 4, 3]

@[expose] def blockHList : List (Perm (Fin 6)) := closureList id id [blockPerm0, blockPerm1] 12

@[expose] def blockTList : List (Perm (Fin 6)) := closureList id id [blockTau2, blockTau3] 6

end CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
