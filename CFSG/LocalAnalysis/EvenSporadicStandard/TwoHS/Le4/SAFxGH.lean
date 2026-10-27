module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyGHWr
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAut3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.EvenSporadicStandard.TwoHS

theorem gh312WrFixed_of_gh312Fixed (h : GH312Fixed) : GH312WrFixed := by
  intro X _ _ hO hZ hP hu
  rcases h X hO hZ hP hu with hS9 | hE | hPG
  · exact Or.inl hS9
  · right
    left
    obtain ⟨P, ⟨ι⟩⟩ := hP
    obtain ⟨ψ⟩ := hE
    have hn : (CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup X)).Normal :=
      ⟨fun k hk g => (CFSG.GorensteinWalter.componentLayerOf_isNormalIn ⊤).2 g trivial k hk⟩
    obtain ⟨hAut⟩ := mulAut_A5A5_equiv_wreath
    exact SAFyGH.equiv_wreath_of_layer hO _ ψ P ι hAut
  · exact Or.inr (Or.inr hPG)

end CFSG.EvenSporadicStandard.TwoHS
