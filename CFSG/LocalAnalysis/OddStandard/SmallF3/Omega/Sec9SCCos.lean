module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sec9CosI1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      ∀ y : G, orderOf y = 2 → y ∈ normalizer (L : Set G) → (∀ b ∈ B, y * b = b * y) →
        ¬ InnerOn L y → ∃ b ∈ B, ∃ α : ℤˣ, InducesTypeSome L (y * b) 6 (-1) 1 α

@[expose] def Asc82Sec9CosIrred : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → (∀ b ∈ B, s * b = b * s) →
        (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) → ∀ B' : Subgroup G, B' ≤ B →
          (∀ x ∈ layerCent L s ⊓ normalizer (B : Set G), (∃ j : ℕ, x ^ (2 ^ j) = 1) →
            ∀ c ∈ B', x * c * x⁻¹ ∈ B') → B' = ⊥ ∨ B' = B

structure Asc82Sec9Cos : Prop where
  exists_i1 : Asc82Sec9CosI1
  irred : Asc82Sec9CosIrred

end CFSG.OddStandard.SmallF3.Omega
