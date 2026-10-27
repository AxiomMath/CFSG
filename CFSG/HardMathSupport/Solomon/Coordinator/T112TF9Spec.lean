module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix

@[expose] def UnitaryH90 (F : Type) [Field F] [Finite F] (q : ℕ) : Prop :=
  Nat.card F = q ^ 2 → ∀ (σ : F ≃+* F) (A : GL (Fin 3) F), σ ^ 3 = 1 → σ ≠ 1 →
    ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 →
    (∃ c : Fˣ, CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.twistedProd σ A 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c) →
    ∃ (M : GL (Fin 3) F) (d : Fˣ),
      ((M : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ * (M : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      A * Matrix.GeneralLinearGroup.map (σ : F →+* F) M =
        Matrix.GeneralLinearGroup.scalar (Fin 3) d * M

end CFSG.HardMathSupport.Solomon.Coordinator
