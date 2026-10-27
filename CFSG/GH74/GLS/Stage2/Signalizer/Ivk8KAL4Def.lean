module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

@[expose] def kaSlCent {F : Type} [Field F] (A : GL (Fin 4) F) : Subgroup SL(4, F) :=
  (Subgroup.centralizer ({A} : Set (GL (Fin 4) F))).comap Matrix.SpecialLinearGroup.toGL

@[expose] def KAL4B3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ B : GL (Fin 4) F, B * B = 1 →
    Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 3 → KAAll (conjAut 4 F B)

@[expose] def KAL4B2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → 5 ≤ Nat.card F → ∀ B : GL (Fin 4) F,
    B * B = 1 → Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2 →
    KAAll (conjAut 4 F B)

@[expose] def KAL4B2Three : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 → ∀ B : GL (Fin 4) F, B * B = 1 →
    Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2 → KAAll (conjAut 4 F B)

@[expose] def KAL4NS : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ (A : GL (Fin 4) F) (c : Fˣ),
    A * A = GeneralLinearGroup.scalar (Fin 4) c → ¬ IsSquare (c : F) → KAAll (conjAut 4 F A)

@[expose] def KAL4GOrth : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → 5 ≤ Nat.card F → ∀ A : GL (Fin 4) F,
    (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A → KAAll (conjAut 4 F A * dualAut 4 F)

@[expose] def KAL4GOrthThree : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 → ∀ A : GL (Fin 4) F,
    (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A → KAAll (conjAut 4 F A * dualAut 4 F)

@[expose] def KAL4GSp : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ A : GL (Fin 4) F,
    (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A → KAAll (conjAut 4 F A * dualAut 4 F)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
