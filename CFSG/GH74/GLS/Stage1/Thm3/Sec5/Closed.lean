module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Stages
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.Blueprint
open scoped commutatorElement

@[expose] def IG_15_16_ext : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P Q₀ N : Subgroup G) (u : G),
    CFSG.ABGLocalTools.IsSylowOf 2 P X → Q₀ ≤ P → Q₀.relIndex P ≤ 2 →
    N ≤ X → (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → Odd (Nat.card ↥N) →
    u ∈ P → orderOf u = 2 → u ∈ ⁅X, X⁆ ⊔ N →
      ∃ x ∈ X, x⁻¹ * u * x ∈ Q₀ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ centralizer ({x⁻¹ * u * x} : Set G))
          (X ⊓ centralizer ({x⁻¹ * u * x} : Set G))

@[expose] def P_normal_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Cfg5 G z S K₁ K₂ →
    ∃ x ∈ Pz S z, orderOf x = 2 ∧ x ≠ z ∧
      ∀ s ∈ S, s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x * z

@[expose] def FStar_C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Qz S z = zpowers z → ∀ c ∈ Cz z, (∀ k ∈ K₁ ⊔ K₂, ⁅k, c⁆ ∈ Oz z) → c ∈ zpowers z ⊔ Oz z

@[expose] def III2_9_5_r2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Qz S z = zpowers z → ∀ a ∈ S, orderOf a = 2 → a ∈ commBar z →
      a ∈ normalizer (K₁ : Set G) → a ∈ normalizer (K₂ : Set G) → InducesInner a K₁ →
        InducesInner a K₂

@[expose] def IVK_1_2j_52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (a : G), Cfg5 G z S K₁ K₂ →
    Elt5 G z S K₁ K₂ a → ∀ A B : Subgroup G, (A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) →
      Qof S B ≠ Pof S A → (Qof S B ⊔ zpowers a) ⊓ Qof S A ≤ zpowers z

@[expose] def IVK_1_9_52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (a : G), Cfg5 G z S K₁ K₂ →
    Elt5 G z S K₁ K₂ a → ∀ A B : Subgroup G, (A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) →
      Qof S B ≠ Pof S A → (Qof S B ⊔ zpowers a) ⊓ Qof S A ≤ zpowers z →
        ∃ _ : ((Pof S A).subgroupOf (Qof S B ⊔ zpowers a)).Normal,
          IsCyclic (↥(Qof S B ⊔ zpowers a) ⧸ (Pof S A).subgroupOf (Qof S B ⊔ zpowers a))

@[expose] def IVK_3_2_lifted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (a x : G),
    Ctr5 G z S K₁ K₂ a x → L52 S K₁ K₂ → L53 z S K₁ K₂ a

@[expose] def IVK_1_3a_52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Cfg5 G z S K₁ K₂ →
    ∀ u ∈ K₁ ⊔ K₂, u * u = 1 → u ≠ 1 → u ≠ z → Group.IsSolvable ↥(centralizer ({z, u} : Set G))

@[expose] def IA_nonsolv_52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a : G) (q₀ : ℕ), Odd q₀ → 3 < q₀ →
    (JClassical4 a q₀ ∨ JG2 a q₀) → ∀ y ∈ centralizer ({a} : Set G), y * y = 1 →
      ¬ Group.IsSolvable ↥(Jof a ⊓ centralizer ({y} : Set G))

@[expose] def IVK_3_2a_strong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) (a : G), Cfg5 G z S K₁ K₂ →
    a ∈ S → orderOf a = 2 → a ≠ z → InducesFAut a K₁ → a ∉ cSec K₁ → a ∈ commBar z →
      InducesFAut a K₂ ∧ a ∉ cSec K₂

@[expose] def IVK_f_inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∀ b : G, InducesFAut b K → b ∈ innSub K → b ∈ cSec K

@[expose] def IVK_f_sq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∀ b : G, InducesFAut b K → b * b ∈ innSub K →
      b * b ∈ cSec K

@[expose] def IVK_f_coset : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∀ s t : G, s ∈ normalizer (K : Set G) →
      t ∈ normalizer (K : Set G) → s * s ∈ cSec K → t * t ∈ cSec K → t ∉ cSec K →
        s * t⁻¹ ∈ innSub K → InducesFAut t K → InducesFAut s K

@[expose] def IVK_f_cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∀ t ∈ S, InducesFAut t K → t ∉ cSec K → t * t ∈ cSec K →
      ∃ y ∈ S ⊓ K, y * y = z ∧ y * t = t * y

@[expose] def P_noncyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ¬ IsCyclic ↥(S ⊓ K)

@[expose] def TwoGroup_coset_sq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Q : Subgroup G) (z b : G), IsPGroup 2 ↥X → Q ≤ X → b ∈ X →
    b ∉ Q → b * b ∈ Q → (∀ x ∈ X, x ∈ Q ∨ x * b⁻¹ ∈ Q) → (∀ u ∈ X, u * u = 1 → u = 1 ∨ u = z) →
      ¬ IsCyclic ↥Q → ∃ t ∈ X, t ∉ Q ∧ t * t = z

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
