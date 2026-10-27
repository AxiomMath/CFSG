module

public import CFSG.Holt.H78.Defs

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt

section Primitive

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

@[expose] def HoltPrimitiveConclusion [Fintype Ω] [DecidableEq Ω] : Prop :=
  alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range ∨
    ∃ q e : ℕ, IsBenderNormal Ω (⊤ : Subgroup G) q e

end Primitive

@[expose] def HoltSection4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
    [FaithfulSMul G Ω], IsStarGroup G Ω → IsPreprimitive G Ω → jHull G Ω = ⊤ →
    CFSG.pPrimeCore 2 G = ⊥ → HoltTheorem1Below (Nat.card G) (Nat.card Ω) →
    HoltPrimitiveConclusion G Ω

end CFSG.Holt.H78
