module

public import CFSG.GH74.GLS.Stage4.T2Defs
public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

variable {G : Type} [Group G]

structure Ch6Coord (N : T2N1 G) : Prop where
  coord₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL2 F →* G), Nat.card F = N.q₁ ∧
    Function.Injective φ ∧ φ.range = N.K₁ ∧ φ (negOne F) = N.z ∧
    N.X₁ = (uSub F).map φ ∧ N.X₁' = (lSub F).map φ ∧ N.w₁ = φ (sl2W F) ∧
    N.H ⊓ N.K₁ = (tSub F).map φ
  coord₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL2 F →* G), Nat.card F = N.q₂ ∧
    Function.Injective φ ∧ φ.range = N.K₂ ∧ φ (negOne F) = N.z ∧
    N.X₂ = (uSub F).map φ ∧ N.X₂' = (lSub F).map φ ∧ N.w₂ = φ (sl2W F) ∧
    N.H ⊓ N.K₂ = (tSub F).map φ

end CFSG.GH74.GLS.Stage4.Rest
