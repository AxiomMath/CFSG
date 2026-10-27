module

public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.LieType.Universal.Spin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsPlusSpace (Q : QuadraticForm (ZMod 2) V) (m : ℕ) : Prop :=
  ∃ φ : V ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2), ∀ v, quadPlus m (ZMod 2) (φ v) = Q v

@[expose] def IsMinusSpace (Q : QuadraticForm (ZMod 2) V) (m : ℕ) : Prop :=
  ∃ φ : V ≃ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2),
    ∀ v, quadMinus m (ZMod 2) 1 1 (φ v) = Q v

@[expose] def IsStdSpace (ε : Bool) (Q : QuadraticForm (ZMod 2) V) (m : ℕ) : Prop :=
  match ε with
  | true => IsPlusSpace Q m
  | false => IsMinusSpace Q m

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
