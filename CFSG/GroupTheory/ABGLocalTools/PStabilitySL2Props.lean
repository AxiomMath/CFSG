module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

open Subgroup

namespace CFSG.ABGLocalTools

@[expose] def TwoSubgroupsCyclic {G : Type*} [Group G] (B : Subgroup G) : Prop :=
  ∀ T : Subgroup G, T ≤ B → IsPGroup 2 T → IsCyclic T

@[expose] def SL2BorelOfSplitElement : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime], p ≠ 2 → Odd (Nat.card F) →
    ¬ p ∣ Nat.card F → ¬ p ∣ Nat.card F + 1 →
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, orderOf g = p →
      ∃ B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), g ∈ B ∧ TwoSubgroupsCyclic B ∧
        pCore p B = ⊥ ∧ ∃ b ∈ B, g * b ≠ b * g

@[expose] def SL2ElementChoice : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime], p ≠ 2 → Odd (Nat.card F) →
    5 < Nat.card F → p ∣ Nat.card F + 1 →
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, orderOf g = p →
      ∃ u : Matrix.SpecialLinearGroup (Fin 2) F,
        ∃ w ∈ closure ({g, u * g * u⁻¹} : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
          (∀ k : ℕ, w ^ p ^ k ≠ 1) ∧ ((p = 3 ∨ p = 5) → w ^ 4 ≠ 1 ∧ w ^ 6 ≠ 1 ∧ w ^ 10 ≠ 1)

@[expose] def SL2DicksonQuotient : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime], p ≠ 2 → Odd (Nat.card F) →
    ¬ p ∣ Nat.card F → ∀ g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) F,
      orderOf g₁ = p → orderOf g₂ = p →
      ((∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p)
          (φ : closure ({g₁, g₂} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) →*
            Matrix.SpecialLinearGroup (Fin 2) K), Function.Surjective φ) ∨
        ∃ φ : closure ({g₁, g₂} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) →*
          Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), Function.Surjective φ) →
      (p = 3 ∨ p = 5) ∧ ∀ w ∈ closure ({g₁, g₂} : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
        w ^ 4 = 1 ∨ w ^ 6 = 1 ∨ w ^ 10 = 1

@[expose] def SL2FieldAutomorphism : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime], p ≠ 2 → Odd (Nat.card F) →
    ¬ p ∣ Nat.card F → ∀ α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F), α ^ p = 1 →
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) F, α ≠ MulAut.conj g) →
      ∃ B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), B.map α.toMonoidHom = B ∧
        TwoSubgroupsCyclic B ∧ pCore p B = ⊥ ∧ ∃ b ∈ B, α b ≠ b

@[expose] def SL2OddNormal : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
    ∀ N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), N.Normal → Odd (Nat.card N) → N = ⊥

end CFSG.ABGLocalTools
