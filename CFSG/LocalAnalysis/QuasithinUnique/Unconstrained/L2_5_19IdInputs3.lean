module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

@[expose] def TabConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    ((PatA X K t ∧ Nat.card (Subgroup.center ↥X) ≤ 2) ∨ (PatB X K t ∧ Subgroup.center ↥X = ⊥) ∨
      PatSp4 X K ∨ PatL5 X K ∨ (PatHS X K t ∧ Subgroup.center ↥X = ⊥)) →
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u

@[expose] def TabJ2Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatB X K t → Nat.card (Subgroup.center ↥X) ≤ 2 →
    ∀ i ∈ centerOf X, i ≠ 1 → ∃ x ∈ X, x⁻¹ * t * x = t * i

@[expose] def TabHSCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    IsPGroup 2 (Subgroup.center ↥X) →
    Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .HS) →
    Subgroup.center ↥X ≠ ⊥ → t ∈ X → t * t = 1 →
    IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G)) → IsA6 K → False

structure Inputs2519Three : Prop extends Inputs2519 where
  conj : TabConj
  j2cover : TabJ2Cover
  hscover : TabHSCover

end CFSG.QuasithinUnique.Id2519
