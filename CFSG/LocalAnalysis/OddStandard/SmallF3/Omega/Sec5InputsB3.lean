module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Fact513Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h,
        x⁻¹ * t * x ∈ DeltaT5 z (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) →
          (x⁻¹ * t * x) * t = t * (x⁻¹ * t * x) →
            CFSG.conjugate (K₁ ⊔ K₂) x = K₁ ⊔ K₂

end CFSG.OddStandard.SmallF3.Omega
