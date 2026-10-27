module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

structure IsGomiLeviPackage {G : Type} [Group G] (L U P : Subgroup G) (ℳ : Set (Subgroup G)) :
    Prop where
  le_parabolic : ∀ M ∈ ℳ, M ≤ P
  inf_eq_bot : ∀ M ∈ ℳ, pCoreOf 2 P ⊓ M = ⊥
  commute : ∀ M₁ ∈ ℳ, ∀ M₂ ∈ ℳ, M₁ ≠ M₂ → ⁅M₁, M₂⁆ = ⊥
  pElementSubgroup_eq : ∀ M ∈ ℳ, pElementSubgroup 2 M = M
  sylow_le : U ≤ pCoreOf 2 P ⊔ sSup ℳ
  normal : ∀ M ∈ ℳ, P ≤ normalizer ((pCoreOf 2 P ⊔ M : Subgroup G) : Set G)
  center_commutator_le : ∀ M ∈ ℳ, ⁅(center ↥M).map M.subtype, P⁆ ≤ pCoreOf 2 P
  atom : ∀ A : Subgroup G, IsGomiAtom L U A → A ≤ P → ∃ M ∈ ℳ,
    A ≤ L ⊓ normalizer (U : Set G) ⊔ M ∧
      ∀ M' ∈ ℳ, A ≤ L ⊓ normalizer (U : Set G) ⊔ M' → M' = M
  factor : ∀ M ∈ ℳ, IsGomiChevTwo ↥M ∨ Nonempty (↥M ≃* Equiv.Perm (Fin 6)) ∨
    L ⊓ normalizer (U : Set G) ⊓ M ⋖ M

@[expose] def GomiChevLeviPackage : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U P : Subgroup G), IsGomiChevTwo ↥L → center ↥L = ⊥ →
    IsSylowOf 2 U L → L ⊓ normalizer (U : Set G) < P → P < L → ¬ IsGomiAtom L U P →
    ∃ ℳ : Set (Subgroup G), IsGomiLeviPackage L U P ℳ

end CFSG.GroupTheory
