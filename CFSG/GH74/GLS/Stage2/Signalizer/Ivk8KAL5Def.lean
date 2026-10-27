module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

@[expose] def kaSlCent5 {F : Type} [Field F] (A : GL (Fin 5) F) : Subgroup SL(5, F) :=
  (Subgroup.centralizer ({A} : Set (GL (Fin 5) F))).comap Matrix.SpecialLinearGroup.toGL

@[expose] def KAL5B4 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ B : GL (Fin 5) F, B * B = 1 →
    Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 4 → KAAll (conjAut 5 F B)

@[expose] def KAL5B3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → 5 ≤ Nat.card F → ∀ B : GL (Fin 5) F,
    B * B = 1 → Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 3 →
    KAAll (conjAut 5 F B)

@[expose] def KAL5B3Three : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 → ∀ B : GL (Fin 5) F, B * B = 1 →
    Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 3 → KAAll (conjAut 5 F B)

@[expose] def KAL5GOrth : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → ∀ A : GL (Fin 5) F,
    (A : Matrix (Fin 5) (Fin 5) F)ᵀ = A → KAAll (conjAut 5 F A * dualAut 5 F)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
