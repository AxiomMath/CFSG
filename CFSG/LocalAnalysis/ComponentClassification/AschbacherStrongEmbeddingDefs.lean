module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

@[expose] def ProductUniqueContainment (H : Subgroup G) (z : G) : Prop :=
  ∀ t ∈ involutionPointClass z, Commute z t → t ≠ z →
    ∀ g : G, g⁻¹ * (z * t) * g ∈ H ↔ g ∈ H

@[expose] def CentralProductCentralizer (H : Subgroup G) (z : G) : Prop :=
  InvolutionPointCentralSylow z ∧
    ∀ t ∈ involutionPointClass z, Commute z t → t ≠ z →
      Subgroup.centralizer ({z * t} : Set G) ≤ H

@[expose] def PointHullStrongSplit [Finite G] (H : Subgroup G) (z : G) : Prop :=
  twoRank (involutionPointHull z) ≤ 1 ∨
    ∃ u : involutionPointHull z, u ^ 2 = 1 ∧
      QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z)) u ∈
        Subgroup.center (involutionPointHull z ⧸ CFSG.oddCore (involutionPointHull z)) ∧
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z)) u) ⊓
        commutator (involutionPointHull z ⧸ CFSG.oddCore (involutionPointHull z)) = ⊥ ∧
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z)) u) ⊔
        commutator (involutionPointHull z ⧸ CFSG.oddCore (involutionPointHull z)) = ⊤ ∧
      fusionStronglyEmbedded
        (H.subgroupOf ⁅involutionPointHull z, involutionPointHull z⁆) ∧
      ∀ t ∈ involutionPointClass z,
        (u : G)⁻¹ * t ∈ ⁅involutionPointHull z, involutionPointHull z⁆

@[expose] def BenderDoubleCoverRigidity : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (Z : Subgroup D) [Z.Normal],
    Z ≤ Subgroup.center D → Nat.card Z = 2 → commutator D = ⊤ →
      fusionIsBenderGroup (D ⧸ Z) →
        ∀ φ : MulAut D, φ * φ = 1 →
          (∃ R : Sylow 2 D, ∀ r ∈ (R : Subgroup D), φ r = r) → φ = 1

@[expose] def relStronglyClosed (Y : Subgroup G) (A : Set G) (S : Subgroup G) : Prop :=
  ∀ a ∈ A, ∀ y ∈ Y, y⁻¹ * a * y ∈ S → y⁻¹ * a * y ∈ A

end CFSG.ComponentClassification.AschbacherStrongEmbedding
