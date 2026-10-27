module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

structure XCtx (X : Type) [Group X] [Finite X] (z t : X) (A T₁ : Subgroup X) : Prop where
  z_sq : z * z = 1
  z_ne_one : z ≠ 1
  t_sq : t * t = 1
  t_ne_one : t ≠ 1
  zt_ne : z ≠ t
  t_central : ∀ x : X, x * t = t * x
  A_L2 : ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ IVK.IsL2 ↥A (fun r => r = q)
  A_perf : ⁅A, A⁆ = A
  A_cen : ∀ a ∈ A, z * a = a * z
  A_norm : ∀ c : X, z * c = c * z → ∀ a ∈ A, c * a * c⁻¹ ∈ A
  two_elt : ∀ c : X, z * c = c * z → (∃ k : ℕ, c ^ (2 ^ k) = 1) → c ∈ zpowers z ⊔ zpowers t ⊔ A
  cen_A : ∀ c : X, z * c = c * z → (∀ a ∈ A, c * a = a * c) → c ∈ zpowers z ⊔ zpowers t
  perfect_le : ∀ P : Subgroup X, (∀ c ∈ P, z * c = c * z) → ⁅P, P⁆ = P → P ≤ A
  T₁_le : T₁ ≤ A
  T₁_pgrp : IsPGroup 2 T₁
  T₁_max : ∀ P : Subgroup X, P ≤ A → IsPGroup 2 P → T₁ ≤ P → P = T₁
  bound : ∀ P : Subgroup X, IsPGroup 2 P → Nat.card ↥P ≤ 2 * Nat.card ↥T₁ ^ 2
  gen4 : Gen4 X

structure StableL {X : Type} [Group X] (z : X) (A L : Subgroup X) : Prop where
  stable : ∀ x ∈ L, z * x * z⁻¹ ∈ L
  A_le : A ≤ L
  moves : ∃ x ∈ L, z * x ≠ x * z

structure OtherL {X : Type} [Group X] (z : X) (A K : Subgroup X) : Prop where
  stable : ∀ x ∈ K, z * x * z⁻¹ ∈ K
  comm_A : ∀ k ∈ K, ∀ a ∈ A, k * a = a * k
  moves : ∃ x ∈ K, z * x ≠ x * z

@[expose] def StableUniqueInvolution : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z t : X) (A T₁ L : Subgroup X), XCtx X z t A T₁ → StableL z A L →
    IsQuasisimple ↥L → (HasSL2Model ↥L Odd ∨ IsDoubleCoverOfAlt ↥L 7) → False

@[expose] def OtherUniqueInvolution : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z t : X) (A T₁ K : Subgroup X), XCtx X z t A T₁ → OtherL z A K →
    t ∈ K → IsQuasisimple ↥K → (HasSL2Model ↥K Odd ∨ IsDoubleCoverOfAlt ↥K 7) → False

@[expose] def StableDoubleCoverAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z t : X) (A T₁ L : Subgroup X), XCtx X z t A T₁ → StableL z A L →
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt ↥L n) → False

@[expose] def StableL34Cover : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z t : X) (A T₁ L : Subgroup X), XCtx X z t A T₁ → StableL z A L →
    IsQuasisimple ↥L → IsL34Quotient ↥L → Monoid.exponent ↥(center ↥L) = 4 → False

@[expose] def DiagonalImpossible : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (z t : X) (A T₁ L : Subgroup X), XCtx X z t A T₁ →
    IsComponent L → CFSG.LocalAnalysis.ComponentInitial.conjSub z⁻¹ L ≠ L →
      ∀ hAB : ⁅L, CFSG.LocalAnalysis.ComponentInitial.conjSub z⁻¹ L⁆ = ⊥,
      A ≤ (CFSG.LocalAnalysis.ComponentInitial.swapDiag hAB).range → False

end CFSG.GH74.GLS.SP.Local
