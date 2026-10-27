module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def Pz (S : Subgroup G) (z : G) : Subgroup G := S ⊓ rigidProduct z

@[expose] def Qz (S : Subgroup G) (z : G) : Subgroup G := S ⊓ rigidSectionCentralizer z

@[expose] def Rz (S : Subgroup G) (z : G) : Subgroup G := Pz S z ⊔ Qz S z

@[expose] def Interchanges (t : G) (K₁ K₂ : Subgroup G) : Prop :=
  conjugate K₁ t = K₂ ∧ conjugate K₂ t = K₁

@[expose] def Hyp4A (S : Subgroup G) (z : G) : Prop :=
  ∀ t ∈ Rz S z, IsConj z t → t = z

end Defs

structure Std4 (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G) : Prop where
  simple : IsKProperSimple G
  rank : 3 ≤ pRank 2 G
  rank_le : pRank 2 G ≤ 4
  gen4 : Gen4 G
  classical : IsStronglyClassicalInvolution G z
  thm2 : ∃ t ∈ centralizer ({z} : Set G), IsConj z t ∧ t ∉ zStar (rigidProduct z)
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))
  comps : {K : Subgroup G | IsRigidRankOneComp z K} = {K₁, K₂}
  ne : K₁ ≠ K₂
  kgh : KGH G

@[expose] def Lemma4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    (∃ t ∈ Rz S z, orderOf t = 2 ∧ IsConj z t ∧ t ≠ z) →
      (∀ u ∈ Pz S z, orderOf u = 2 → IsConj z u) ∧ Qz S z = zpowers z

@[expose] def Lemma4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Hyp4A S z → ∃ t ∈ S, IsConj z t ∧ t ≠ z ∧ Interchanges t K₁ K₂

@[expose] def Lemma4_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Hyp4A S z → ∀ t ∈ S, IsConj z t → t ≠ z → Interchanges t K₁ K₂ →
      Qz S z = zpowers z ∧ (∀ u ∈ Pz S z, orderOf u = 2 → u ≠ z → IsConj (t * z) u) ∧
        ¬ IsConj z (t * z)

@[expose] def Prop4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Qz S z = zpowers z ∧
    ((∀ u ∈ Pz S z, orderOf u = 2 → IsConj z u) ∨
      ∃ t ∈ S, IsConj z t ∧ t ≠ z ∧ Interchanges t K₁ K₂ ∧
        (∀ u ∈ Pz S z, orderOf u = 2 → u ≠ z → IsConj (t * z) u) ∧ ¬ IsConj z (t * z)) ∧
    ∀ t ∈ centralizer ({z} : Set G), IsConj z t → Interchanges t K₁ K₂ →
      ∀ g : G, g⁻¹ * z * g = t → Interchanges z (conjugate K₁ g) (conjugate K₂ g)

@[expose] def II4_4_4_center : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (z : G), orderOf z = 2 →
    ∀ (S K : Subgroup G), CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)) →
      IsPCompIn 2 (centralizer ({z} : Set G)) K → pRank 2 ↥K = 1 →
        Nat.card ↥(S ⊓ zStar K) = 2 ∧ 8 ≤ Nat.card ↥(S ⊓ K)

@[expose] def IVK_3_1a_lifted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ u v : G, u ∈ K₁ ⊔ K₂ → v ∈ K₁ ⊔ K₂ → u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ z →
      v ≠ z → ∃ k ∈ K₁ ⊔ K₂, k * u * k⁻¹ = v

@[expose] def IVK_1_9_lifted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ t ∈ S, orderOf t = 2 → t ∈ normalizer (K₁ : Set G) → ¬ InducesFAut t K₁ →
      (∃ n, IVK.IsSemidihedralTwoGroup ↥(Pz S z ⊓ K₁ ⊔ zpowers t) n) ∨
        ∃ u ∈ K₁, t * u = u * t ∧ 4 ≤ orderOf u ∧ 2 * orderOf u = Nat.card ↥(Pz S z ⊓ K₁)

@[expose] def IVK_1_2f_lifted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup G)), ∀ y : G, IsPGroup 2 (zpowers y) →
      y ∈ normalizer (K : Set G) → orderOf (y * y) = 2 → ¬ InducesFAut (y * y) K →
        ∃ k ∈ K, y * y * k⁻¹ ∈ centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def L45_balance_step : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Hyp4A S z → ∀ t ∈ S, IsConj z t → t ≠ z → Interchanges t K₁ K₂ →
      ∀ u₁ ∈ K₁, u₁ ∈ S → u₁ * u₁ = z →
        IsConj (u₁ * (t * u₁ * t)) (t * (u₁ * (t * u₁ * t)))

@[expose] def SD_involution_fusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P : Subgroup X) (z t : X), IsPGroup 2 ↥P → z ∈ P →
    z * z = 1 → z ≠ 1 → (∀ x ∈ P, x * z = z * x) → (∀ x ∈ P, x * x = 1 → x = 1 ∨ x = z) →
      t * t = 1 → t ∉ P → (∀ x ∈ P, t * x * t ∈ P) →
      (∃ n, IVK.IsSemidihedralTwoGroup ↥(P ⊔ zpowers t) n) →
        (∃ u₁ ∈ P, u₁ * u₁ = z ∧ t * u₁ * t = u₁⁻¹ ∧ ∃ x ∈ P, x⁻¹ * t * x = t * u₁) ∧
        ∃ y ∈ P, y⁻¹ * t * y = t * z

end CFSG.GH74.GLS.Stage1.Thm3.Sec4
