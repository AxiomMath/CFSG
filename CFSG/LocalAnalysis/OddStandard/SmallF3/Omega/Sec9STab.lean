module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Tab9M : Prop where
  i3_outer : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, s ∈ normalizer (L : Set G) → (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) →
      ¬ InnerOn L s
  cent_B_i3 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      ∀ y : G, y ∈ normalizer (L : Set G) → (∀ b ∈ B, y * b = b * y) → ¬ InnerOn L y →
        ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
          ∃ b ∈ B, ∃ c ∈ centralizer (L : Set G), x = b * c ∨ x = b * y * c

end CFSG.OddStandard.SmallF3.Omega
