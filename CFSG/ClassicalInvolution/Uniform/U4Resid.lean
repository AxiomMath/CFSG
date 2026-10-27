module

public import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

variable (F : Type) [Group F] [Finite F]

@[expose] def SymOuterInput : Prop :=
  ∀ {X Y : Subgroup F} {x y : F}, Mem3 X x → Mem3 Y y → x ∈ Subgroup.normalizer (Y : Set F) →
    (∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a) → y ∈ Subgroup.normalizer (X : Set F)

end CFSG.ClassicalInvolution.Uniform.U4
