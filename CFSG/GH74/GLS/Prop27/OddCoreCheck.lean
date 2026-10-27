module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.GH74.GLS.Prop27

variable {n : ℕ}

@[expose] def oddCoreAt (m : ℕ) (CA CP : List (Equiv.Perm (Fin n))) : Bool :=
  CA.all fun x =>
    bif decide (x ≠ 1) && decide (x ^ m = 1) then
      CP.any fun c => decide ((x * c * x⁻¹ * c⁻¹) ^ m ≠ 1)
    else true

@[expose] def oddCoreCheck (m : ℕ) (LA LP : List (Equiv.Perm (Fin n))) : Bool :=
  LA.all fun τ =>
    bif decide (τ ^ 2 = 1) && decide (τ ≠ 1) then
      oddCoreAt m (LA.filter fun g => decide (g * τ = τ * g))
        (LP.filter fun c => decide (c * τ = τ * c))
    else true

end CFSG.GH74.GLS.Prop27
