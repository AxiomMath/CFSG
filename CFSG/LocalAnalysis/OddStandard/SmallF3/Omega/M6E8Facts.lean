module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82E8LayerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Y R : Subgroup G), IsQuasisimple ↥X → IsQuasisimple ↥Y →
    IsL29 X → IsOmega6Minus Y → X ≤ Y → IsPGroup 2 ↥R →
    R ≤ normalizer (Y : Set G) ⊓ centralizer (X : Set G) →
    (centralizer (Y : Set G)).relIndex R = 4 →
      (∃ r ∈ R, IsOmega5 (layerCent Y r)) ∧
      ∀ r ∈ R, IsOmega5 (layerCent Y r) →
        IsQuasisimple ↥(layerCent Y r) ∧ X ≤ layerCent Y r ∧
        R ⊓ centralizer (layerCent Y r : Set G) ≤ (R ⊓ centralizer (Y : Set G)) ⊔ zpowers r

@[expose] def Asc82AutCentOmega5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X J R : Subgroup G), IsQuasisimple ↥X → IsQuasisimple ↥J →
    IsL29 X → IsOmega5 J → X ≤ J → IsPGroup 2 ↥R →
    R ≤ normalizer (J : Set G) ⊓ centralizer (X : Set G) →
      (centralizer (J : Set G)).relIndex R ≤ 2

end CFSG.OddStandard.SmallF3.Omega
