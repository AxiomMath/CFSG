module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Fixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.SolomonRed

theorem lemmaR {G B : Type*} [Group G] [Finite G] [Group B] {B₀ : Subgroup B}
    (hR : RHyp B B₀) (hO : fusionOddCore G = ⊥) {t : G} (ht : orderOf t = 2)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) :
    t ∈ Subgroup.center G ∨
      (Setting G t (B₀.map (embA ζ)) ∧
        ((∃ S₁ S₂ : Subgroup G, SwapData G t (B₀.map (embA ζ)) S₁ S₂) ∨
          ∃ S : Subgroup G, FixedData G S ∧ B₀.map (embA ζ) ≤ S)) := by
  by_cases htc : t ∈ Subgroup.center G
  · exact Or.inl htc
  · right
    have hS := setting_of_RHyp hR hO ht ζ htc
    refine ⟨hS, ?_⟩
    rcases dichotomy hS with ⟨S, hF⟩ | ⟨S₁, S₂, hs⟩
    · exact Or.inr ⟨S, hF, setting_le_of_fixedData hS hF⟩
    · exact Or.inl ⟨S₁, S₂, hs⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent
