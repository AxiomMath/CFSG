module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Split47Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    (¬ ∃ h : G, h⁻¹ * t * h = t * z) → ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      ∃ K : Subgroup G, K ≤ centralizer ({t} : Set G) ⊓ normalizer (A : Set G) ∧
        K.relIndex (centralizer ({t} : Set G) ⊓ normalizer (A : Set G)) = 2 ∧ t ∉ K

end CFSG.OddStandard.SmallF3.Omega
