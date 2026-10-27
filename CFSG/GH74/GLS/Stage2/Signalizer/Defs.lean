module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement Matrix MatrixGroups

section Sections

variable {G : Type} [Group G]

abbrev Sec (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] : Type := ↥H₀ ⧸ H₁

@[expose] def zSec (z : G) (H₀ : Subgroup G) (hz : z ∈ H₀) (H₁ : Subgroup ↥H₀) [H₁.Normal] :
    Sec H₀ H₁ := QuotientGroup.mk ⟨z, hz⟩

@[expose] def ncl {A : Type} [Group A] (X : Subgroup A) : Subgroup A := Subgroup.normalClosure (X : Set A)

@[expose] def nclIn (H X : Subgroup G) : Subgroup G :=
  (Subgroup.normalClosure ((X.subgroupOf H : Subgroup ↥H) : Set ↥H)).map H.subtype

end Sections

structure Sig4A {A : Type} [Group A] (z : A) (H : Subgroup A) (p : ℕ) (X : Subgroup A) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  z_mem : z ∈ H
  X_le : X ≤ H
  pgroup : IsPGroup p ↥X
  ne_bot : X ≠ ⊥
  inv : ∀ c ∈ H, c ∈ centralizer ({z} : Set A) → c ∈ normalizer (X : Set A)
  comm : ⁅X, zpowers z⁆ = X

structure Sig4Sub (G : Type) [Group G] (z : G) (H : Subgroup G) (p : ℕ) (X : Subgroup G) : Prop where
  proper : H ≠ ⊤
  A : Sig4A z H p X

structure Sig4B (G : Type) [Group G] (z : G) (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal]
    (hz : z ∈ H₀) (p : ℕ) (X : Subgroup (Sec H₀ H₁)) : Prop where
  proper : H₀ ≠ ⊤
  odd : Odd (Nat.card ↥H₁)
  A : Sig4A (zSec z H₀ hz H₁) (⊤ : Subgroup (Sec H₀ H₁)) p X
  op : pCore p (Sec H₀ H₁) = ⊥

@[expose] def IsPGL3Four (K : Type) [Group K] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (K ≃* Matrix.ProjGenLinGroup (Fin 3) F)

section Parabolic

variable {A : Type} [Group A]

@[expose] def IsParabolicP (p : ℕ) (K P : Subgroup A) : Prop :=
  P ≤ K ∧ ∃ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf p U K ∧ K ⊓ normalizer (U : Set A) ≤ P

@[expose] def IsMaxParabolicP (p : ℕ) (K P : Subgroup A) : Prop :=
  IsParabolicP p K P ∧ P ≠ K ∧ ∀ Q : Subgroup A, IsParabolicP p K Q → Q ≠ K → P ≤ Q → Q = P

end Parabolic

section TCases

variable {G : Type} [Group G]

@[expose] def OneClassInv (G : Type) [Group G] : Prop :=
  ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v

@[expose] def TypeOneCase (G : Type) [Group G] (k : Kind) : Prop := OneClassInv G ∨ k = Kind.m12

@[expose] def T4C (z : G) (k : Kind) (S T : Subgroup G) : Prop :=
  (TypeOneCase G k ∧ T = S) ∨
    (¬ TypeOneCase G k ∧ ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ z ∈ U ∧ (∃ t ∈ U, SwapsComps z t) ∧
      pLayerOf 2 (centralizer (U : Set G)) ≠ ⊥ ∧ T = S ⊓ centralizer (U : Set G))

@[expose] def T5A (z : G) (k : Kind) (S T Tstar : Subgroup G) : Prop :=
  (TypeOneCase G k ∧ T = S ∧ Tstar = S) ∨
    (¬ TypeOneCase G k ∧ ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ z ∈ U ∧
      (∃ t ∈ U, SwapsComps z t) ∧ CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer (U : Set G)) ∧ T ≤ S ∧
      Tstar = pLayerOf 2 (centralizer (U : Set G)) ⊔ T)

@[expose] def Covers (A B C : Subgroup G) : Prop := B ≤ (A ⊓ B) ⊔ C

@[expose] def InvCover (p : ℕ) (H T Tstar Q : Subgroup G) : Prop :=
  Q ≤ H ∧ IsPGroup p ↥Q ∧ T ≤ normalizer (Q : Set G) ∧
    Covers (H ⊓ normalizer (Q : Set G)) Tstar (pPrimeCoreOf 2 Tstar)

@[expose] def MaxInv (p : ℕ) (H T Tstar P : Subgroup G) : Prop :=
  InvCover p H T Tstar P ∧ ∀ Q : Subgroup G, InvCover p H T Tstar Q → P ≤ Q → Q = P

end TCases

section Small

variable {G : Type} [Group G]

@[expose] def SDorWr (S : Subgroup G) : Prop :=
  (∃ n : ℕ, IVK.IsSemidihedralTwoGroup ↥S n) ∨ ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥S ≃* CFSG.Open.WreathedTwoGroup n)

@[expose] def omega1Z (p : ℕ) (P : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ P ∧ (∀ y ∈ P, x * y = y * x) ∧ x ^ p = 1}
  one_mem' := ⟨one_mem _, fun y _ => by simp, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨haP, hac, hap⟩ ⟨hbP, hbc, hbp⟩
    refine ⟨mul_mem haP hbP, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · rw [Commute.mul_pow (hac b hbP), hap, hbp, one_mul]
  inv_mem' := by
    rintro a ⟨haP, hac, hap⟩
    refine ⟨inv_mem haP, fun y hy => ?_, by rw [inv_pow, hap, inv_one]⟩
    exact (Commute.inv_left (hac y hy)).eq

@[expose] def oddPart (n : ℕ) : ℕ := n / 2 ^ n.factorization 2

end Small

end CFSG.GH74.GLS.Stage2.Signalizer
