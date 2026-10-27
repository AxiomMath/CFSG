module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def SD_sq_not_z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (z y : G),
    (∃ n, IVK.IsQuaternionTwoGroup ↥P n) → z ∈ P → z * z = 1 → z ≠ 1 → y * y = 1 → y ∉ P →
    (∀ p ∈ P, y * p * y⁻¹ ∈ P) → (∃ n, IVK.IsSemidihedralTwoGroup ↥(P ⊔ zpowers y) n) →
      ∀ v ∈ P, (v * y) * (v * y) ≠ z

@[expose] def Quat_centr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Subgroup G) (z u : G) (n : ℕ),
    IVK.IsQuaternionTwoGroup ↥P n → z ∈ P → z * z = 1 → z ≠ 1 → u ∈ P → u * u = z →
    (∀ p ∈ P, p * u * p⁻¹ = u ∨ p * u * p⁻¹ = u * z) →
      IsCyclic ↥(P ⊓ centralizer ({u} : Set G)) ∧ (P ⊓ centralizer ({u} : Set G)).relIndex P = 2

@[expose] def IVK_SR_abelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ Rz S z

@[expose] def II4_ord4_R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F → IsCyclic ↥F →
    ∀ w ∈ Rz S z, ∀ w' ∈ Rz S z, w * w = 1 → w' * w' = 1 → w ≠ 1 → w ≠ z → w' ≠ 1 → w' ≠ z →
      IsConj w w'

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
