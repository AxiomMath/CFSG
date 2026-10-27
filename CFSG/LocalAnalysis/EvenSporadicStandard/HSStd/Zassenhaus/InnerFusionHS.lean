module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSSpecial

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem hsInnerFusion_of_innerData_hs
    (hdata : ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G) (z : G), IsSporadic L .HS →
      IsPGroup 2 S → ¬ 2 ∣ (S ⊓ L).relIndex L → z ∈ S ⊓ L → orderOf z = 2 →
      centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z → Nonempty (InnerData L z)) :
    HSInnerFusion :=
  hsInnerFusion_of_innerData hdata
    (fun _ _ _ _ _ hL hS hSL hz hz2 hcent => exists_special_of_sylow hL hS hSL hz hz2 hcent)
    (fun _ _ _ _ _ hL hS hSL hz hz2 hcent _ _ h₁ h₂ hab₁ hab₂ hc₁ hc₂ hz₁ hz₂ hcj₁ hcj₂ =>
      special_unique_of_sylow hL hS hSL hz hz2 hcent h₁ h₂ hab₁ hab₂ hc₁ hc₂ hz₁ hz₂ hcj₁ hcj₂)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
