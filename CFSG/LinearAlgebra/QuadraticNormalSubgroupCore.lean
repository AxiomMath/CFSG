module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LinearAlgebra

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def linearAction (U : Subgroup (V ≃ₗ[ZMod 2] V)) : U →* MulAut (Multiplicative V) where
  toFun u := AddEquiv.toMultiplicative (u : V ≃ₗ[ZMod 2] V).toAddEquiv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

variable [Finite V]

end CFSG.LinearAlgebra
