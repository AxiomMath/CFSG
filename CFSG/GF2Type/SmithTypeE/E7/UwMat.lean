module

public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.GF2Type.SmithTypeE.E7

open scoped Matrix

abbrev M6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

abbrev GL6 : Type := Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)

@[expose] def IsUT (A : M6) : Prop := ∀ i j : Fin 6, j ≤ i → A i j = if i = j then 1 else 0

@[expose] def IsAlt (N : M6) : Prop := Nᵀ = N ∧ ∀ i, N i i = 0

@[expose] def rkA (i j : Fin 6) : ℕ := 6 * (j.val - i.val) + i.val

@[expose] def rkN (k l : Fin 6) : ℕ :=
  6 * (20 - (min k.val l.val + max k.val l.val)) + min k.val l.val

@[expose] def LeadA (A : M6) (i j : Fin 6) : Prop :=
  i < j ∧ (A - 1) i j = 1 ∧ ∀ a b : Fin 6, a < b → rkA a b < rkA i j → (A - 1) a b = 0

@[expose] def LeadN (N : M6) (k l : Fin 6) : Prop :=
  k < l ∧ N k l = 1 ∧ ∀ a b : Fin 6, a < b → rkN a b < rkN k l → N a b = 0

end CFSG.GF2Type.SmithTypeE.E7
