module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def Q_DSD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    2 ≤ pRank 2 ↥(Qof S K) →
      ∃ u₀ ∈ Qof S K, u₀ * u₀ = z ∧ (∀ s ∈ S, s * u₀ * s⁻¹ = u₀ ∨ s * u₀ * s⁻¹ = u₀ * z) ∧
        ∀ b ∈ Qof S K, b * b = 1 → b ≠ 1 → b ≠ z → b * u₀ * b⁻¹ = u₀ * z

@[expose] def IVK_fAut_r1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    (∀ b : G, InducesFAut b K → b ∈ innSub K → b ∈ cSec K) ∧
    (∀ b : G, InducesFAut b K → b * b ∈ innSub K → b * b ∈ cSec K) ∧
    (∀ s t : G, s ∈ normalizer (K : Set G) → t ∈ normalizer (K : Set G) → s * s ∈ cSec K →
      t * t ∈ cSec K → t ∉ cSec K → s * t⁻¹ ∈ innSub K → InducesFAut t K → InducesFAut s K) ∧
    (∀ t ∈ S, InducesFAut t K → t ∉ cSec K → t * t ∈ cSec K → ∃ y ∈ S ⊓ K, y * y = z ∧ y * t = t * y)

@[expose] def IVK_3_2a_r1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    ∀ a ∈ S, orderOf a = 2 → a ≠ z → InducesFAut a K → a ∉ cSec K → a ∉ commBar z

@[expose] def TwoGroup_coset_sq_gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Q : Subgroup G) (z b : G), IsPGroup 2 ↥X → Q ≤ X → b ∈ X →
    b ∉ Q → b * b ∈ Q → (∀ x ∈ X, x ∈ Q ∨ x * b⁻¹ ∈ Q) → (∀ u ∈ X, u * u = 1 → u = 1 ∨ u = z) →
      ¬ IsCyclic ↥X → ∃ t ∈ X, t ∉ Q ∧ t * t = z

@[expose] def Lem510_cyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    pRank 2 ↥(Qof S K) = 1 → ∀ b ∈ S, b * b ∈ Qof S K → InducesFAut b K → b ∉ cSec K →
      IsCyclic ↥(Qof S K ⊔ zpowers b) → ∃ F : Subgroup G, Std4r1 G z S K F ∧ IsCyclic ↥F

@[expose] def IVK_f_pow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ s ∈ S, InducesFAut s K → s ∉ cSec K →
      ∃ b ∈ S, InducesFAut b K ∧ b ∉ cSec K ∧ b * b ∈ cSec K

@[expose] def IVK_triv_fAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ a ∈ cSec K, InducesFAut a K

@[expose] def IVK_f_sq_R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Std6 G z S →
    (∀ K' : Subgroup G, IsRigidRankOneComp z K' → pRank 2 ↥(Qof S K') = 1) →
      ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ b ∈ S, InducesFAut b K → b * b ∈ cSec K →
        b * b ∈ Rz S z

@[expose] def Prop5_9_r1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    2 ≤ pRank 2 ↥(Qof S K) → ∀ a ∈ Qof S K, orderOf a = 2 → a ≠ z → a ∉ commBar z

@[expose] def Lemma5_10_r1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K : Subgroup G), Std6r1 G z S K →
    pRank 2 ↥(Qof S K) = 1 → ∀ b ∈ S, b * b ∈ Rz S z → InducesFAut b K → b ∉ cSec K →
      ∃ a ∈ S, orderOf a = 2 ∧ InducesFAut a K ∧ a ∉ commBar z

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
