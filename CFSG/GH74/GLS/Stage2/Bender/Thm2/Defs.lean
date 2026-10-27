module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Ctx9

variable {G : Type} [Group G]

@[expose] def Hyp9A (z : G) : Prop :=
  ∀ N ∈ maximalOverCentralizer z, ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Fs N = Op p N

@[expose] def NN (z : G) (p : ℕ) (R X : Subgroup G) : Prop :=
  X ≤ R ∧ X ≠ ⊥ ∧ z ∈ normalizer (X : Set G) ∧
    Fs (normalizer (X : Set G)) = Op p (normalizer (X : Set G))

end Ctx9

structure Ctx9 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) : Prop where
  ctx : Stage2Ctx G z k S
  hyp : Hyp9A z
  mem : M ∈ maximalOverCentralizer z
  prime : p.Prime
  odd : p ≠ 2
  fstar : Fs M = Op p M

section Families

variable {G : Type} [Group G]

@[expose] def TransOn (U : Subgroup G) : Prop :=
  ∀ a ∈ U, a ≠ 1 → ∀ b ∈ U, b ≠ 1 → ∃ n ∈ normalizer (U : Set G), n * a * n⁻¹ = b

@[expose] def Iof (U : Subgroup G) : Subgroup G := pLayerOf 2 (centralizer (U : Set G))

@[expose] def Cov10 (k : Kind) (U A : Subgroup G) : Prop :=
  ¬ TypeOneCase G k → Covers A (Iof U) (pPrimeCoreOf 2 (Iof U))

@[expose] def HOK (k : Kind) (T U H : Subgroup G) : Prop :=
  T ≤ normalizer (H : Set G) ∧ Cov10 k U H

@[expose] def R0 (k : Kind) (p : ℕ) (T U H R : Subgroup G) : Prop :=
  R ≠ ⊥ ∧ IsPGroup p ↥R ∧ R ≤ H ∧ T ≤ normalizer (R : Set G) ∧ Cov10 k U (H ⊓ normalizer (R : Set G))

@[expose] def Rp (z : G) (k : Kind) (p : ℕ) (T U Q M R : Subgroup G) : Prop :=
  R0 k p T U M R ∧ ⁅Q ⊓ normalizer (R : Set G), zpowers z⁆ ≠ ⊥

@[expose] def MaxIn (𝒮 : Set (Subgroup G)) (R : Subgroup G) : Prop :=
  R ∈ 𝒮 ∧ ∀ R' ∈ 𝒮, R ≤ R' → R' = R

@[expose] def MaxSInv (r : ℕ) (S H V : Subgroup G) : Prop :=
  V ≤ H ∧ IsPGroup r ↥V ∧ S ≤ normalizer (V : Set G) ∧
    ∀ W : Subgroup G, W ≤ H → IsPGroup r ↥W → S ≤ normalizer (W : Set G) → V ≤ W → W = V

end Families

structure Choice10 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M T U : Subgroup G) (t g : G) :
    Prop where
  U_le : U ≤ S
  U_four : IVK.IsFourSubgroup U
  U_gen : U = zpowers z ⊔ zpowers t
  t_conj : t = g⁻¹ * z * g
  t_out : ∀ m ∈ M, m⁻¹ * z * m ≠ t
  T_one : TypeOneCase G k → T = S ∧ ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U
  T_two : ¬ TypeOneCase G k → T = S ⊓ centralizer (U : Set G) ∧ SwapsComps z t ∧
    CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer (U : Set G)) ∧ Iof U ≠ ⊥ ∧ z ∈ ⁅Cen z, zpowers t⁆
  trans : TypeOneCase G k → TransOn U
  z_star : z ∈ zStar M ∨ U ⊓ O2Of M = zpowers z
  z_star_one : TypeOneCase G k → z ∈ zStar M

structure Ctx10 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (Q T U : Subgroup G) (t g : G) : Prop where
  ctx9 : Ctx9 G z k S M p
  Q_mem : QP z p (Op p M) Q
  choice : Choice10 G z k S M T U t g

end CFSG.GH74.GLS.Stage2.Bender.Thm2
