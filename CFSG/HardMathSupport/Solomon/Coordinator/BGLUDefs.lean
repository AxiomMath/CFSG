module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open CFSG.Open
open scoped Matrix

variable {F : Type*} [Field F]

@[expose] def fixGL (σ : F ≃+* F) : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F) :=
  (Matrix.GeneralLinearGroup.map σ.toRingHom).eqLocus (MonoidHom.id _)

@[expose] def SU3SubfieldJoin : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (q : ℕ), Nat.card F = q ^ 2 → q % 3 ≠ 0 → q ≠ 8 →
    ∀ σ : F ≃+* F, orderOf σ = 3 →
      ∀ h : Matrix.GeneralLinearGroup (Fin 3) F,
        ((h : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ * (h : Matrix (Fin 3) (Fin 3) F) = 1 →
        (¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * (h : Matrix (Fin 3) (Fin 3) F) i j) =
          c * (h : Matrix (Fin 3) (Fin 3) F) i j) →
        StatedSU 3 q F ≤ (StatedSU 3 q F ⊓ fixGL σ) ⊔
          (StatedSU 3 q F ⊓ fixGL σ).map (MulAut.conj h).toMonoidHom

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
