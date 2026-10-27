module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Tab7P : Prop where
  hyp62_of_sylow : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ H S₁ : Subgroup G, L ≤ H → H ≤ normalizer (L : Set G) → IsSylow2Of S₁ H →
      (∀ n ∈ normalizer (L : Set G), ∃ h ∈ H, ∃ c ∈ centralizer (L : Set G), n = h * c) →
      ∀ B : Subgroup G, IsNormalE16In (S₁ ⊓ L) B →
        (∀ y ∈ S₁, y ∉ centralizer (L : Set G) → (∀ b ∈ B, y * b = b * y) →
          ¬ ∃ α : ℤˣ, InducesTypeSome L y 6 1 1 α) → Hyp62At L
  aut_B_types : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, IsNormalE16In P B →
      ∀ φ : (Fin 5 → ZMod 2) → G,
        IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) ⊤ →
          (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 2 →
            InducesTypeSome L (φ v) 6 1 2 (-1)) ∧
          (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 4 → IsI4PlusIn L (φ v))

end CFSG.OddStandard.SmallF3.Omega
