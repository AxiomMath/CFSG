module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Defs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Bg.TwoGroups.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Setup8_exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Fused8 G z S K₁ K₂ →
    ∃ (W₁ W₂ U : Subgroup G) (u h : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h

@[expose] def G2Shape {X : Type} [Group X] (S A : Subgroup X) (a t y : X) (n : ℕ) : Prop :=
  orderOf a = 2 ^ n ∧ A = zpowers a ⊔ zpowers (t⁻¹ * a * t) ∧
    zpowers a ⊓ zpowers (t⁻¹ * a * t) = ⊥ ∧ a * (t⁻¹ * a * t) = (t⁻¹ * a * t) * a ∧
    t * t = 1 ∧ y * y = 1 ∧ t * y = y * t ∧ t ≠ 1 ∧ y ≠ 1 ∧ t ≠ y ∧
    A ⊓ (zpowers t ⊔ zpowers y) = ⊥ ∧ (∀ x ∈ A, y * x * y = x⁻¹) ∧
    S = A ⊔ zpowers t ⊔ zpowers y

@[expose] def G2_Sylow_shape : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S A : Subgroup X) (a t y : X) (n : ℕ), 2 ≤ n →
    G2Shape S A a t y n → ∀ p f : ℕ, p.Prime → p ≠ 2 → 0 < f →
      ((p ^ f) ^ 2 - 1).factorization 2 = n + 1 →
        ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs), LieModel Gs .G2 0 p f ∧
          ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs))

@[expose] def C1_of_Fused : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Fused8 G z S K₁ K₂ →
    S = S1 S K₁ → (Pz S z).relIndex S = 2 → Nat.card ↥(Pof S K₁) = Nat.card ↥(Pof S K₂) →
      ∃ q : ℕ, (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ f = q ∧
          (q ^ 2 - 1).factorization 2 = (Nat.card ↥(Pof S K₁)).factorization 2) ∧
        HasSL2ProductOfIndexTwoStage1 (oPrimeResidual 2 (CentralizerBar z)) q

@[expose] def IV2_2_9_no_S3 : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* Bg.TwoGroups.SylSU3_4) →
    ∀ H : Subgroup (MulAut T), ¬ Nonempty (↥H ≃* Equiv.Perm (Fin 3))

structure EData {G : Type} [Group G] (Y U E₁ E₂ : Subgroup G) : Prop where
  le₁ : E₁ ≤ Y
  le₂ : E₂ ≤ Y
  elem₁ : Bg.TwoGroups.IsElemAbelian 2 E₁
  elem₂ : Bg.TwoGroups.IsElemAbelian 2 E₂
  card₁ : Nat.card ↥E₁ = 16
  card₂ : Nat.card ↥E₂ = 16
  inter : E₁ ⊓ E₂ = U
  prod : E₁ ⊔ E₂ = Y
  invol : ∀ y ∈ Y, orderOf y = 2 → y ∈ E₁ ∨ y ∈ E₂
  comm : ∀ e ∈ E₁, ∀ f ∈ E₂, e * f * e⁻¹ * f⁻¹ ∈ U

@[expose] def Y34_E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y U : Subgroup G), Nonempty (↥Y ≃* Bg.TwoGroups.SylSL3_4) →
    U ≤ Y → IVK.IsFourSubgroup U → NormedBy U Y → ∃ E₁ E₂ : Subgroup G, EData Y U E₁ E₂

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
