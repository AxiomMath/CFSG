module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactAutOm6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, orderOf t = 2 → centerIn L = zpowers t → ∀ z : G, IsI4PlusIn L z →
      ∀ b : G, orderOf b = 2 → b ∈ normalizer (L : Set G) →
        twoRes (L ⊓ centralizer ({z} : Set G)) ≤ centralizer ({b} : Set G) →
          L ≤ centralizer ({b} : Set G) ∨ L ≤ centralizer ({b * z} : Set G) ∨
            (IsQuasisimple (layerCent L b) ∧
              twoRes (L ⊓ centralizer ({z} : Set G)) ≤ layerCent L b)

@[expose] def Asc82Fact513AModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      A ⊓ (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) ≤
        centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)

end CFSG.OddStandard.SmallF3.Omega
