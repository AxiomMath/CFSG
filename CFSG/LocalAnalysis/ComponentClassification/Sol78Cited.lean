module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS

@[expose] def BalanceTwoComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S T : Subgroup G), S ≠ ⊥ → T ≠ ⊥ →
    IsElementaryAbelian 2 S → IsElementaryAbelian 2 T → S ≤ centralizer (T : Set G) →
    let X := pPrimeCoreOf 2 (centralizer (S : Set G)) ⊓ centralizer (T : Set G)
    let O := pPrimeCoreOf 2 (centralizer (T : Set G))
    ⁅(pPrimePCore 2 ↥(centralizer (T : Set G))).map (centralizer (T : Set G)).subtype, X⁆ ≤ O ∧
    (∀ L : Subgroup G, IsPCompIn 2 (centralizer (T : Set G)) L →
      X ≤ normalizer ((O ⊔ L : Subgroup G) : Set G) ∧
      (¬ ⁅L, X⁆ ≤ O → S ⊓ normalizer (L : Set G) ≠ ⊥ ∧ O ⊔ L = O ⊔ ⁅L, X⁆ ∧
        O ⊔ L = O ⊔ ⁅L, S ⊓ normalizer (L : Set G)⁆)) ∧
    (¬ X ≤ O → ∃ M : Subgroup G, IsPCompIn 2 (centralizer (T : Set G)) M ∧ ¬ ⁅M, X⁆ ≤ O)

@[expose] def StronglyClosedResidualInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), IsPGroup 2 S →
    IsStronglyClosedIn (normalizer (S : Set G)) (S : Set G) →
    ((perfectResidual ↥(centralizer (S : Set G))).map (centralizer (S : Set G)).subtype ⊔
      (pPrimeCore 2 G)).Normal

end CFSG.ComponentClassification.Sol78
