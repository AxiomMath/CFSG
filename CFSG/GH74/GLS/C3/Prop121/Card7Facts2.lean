module

public import CFSG.GH74.GLS.C3.Prop121.Card7Defs
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2

structure SylFacts : Prop where
  count14 : ∀ S' : Sylow 2 A11,
    Nat.card {v : (S' : Subgroup A11) // orderOf (v : A11) = 2 ∧
      numMoved ((v : A11) : Perm (Fin 11)) = 4} = 14

end CFSG.GH74.GLS.C3.Prop121.Card7
