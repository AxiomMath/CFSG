module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Main
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma23

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

theorem h64_prop : H64Prop SylSL3_4 SylSU3_4 := by
  intro T _ _ hcard α hord hfix A hAn hAα hθ hCA
  obtain ⟨hU, hL⟩ := iv2_2_3 T hcard α hord hfix A hAn hAα hθ hCA
  by_cases h : Om1 A = Om1 (⊤ : Subgroup T)
  · exact Or.inr (Or.inr (Or.inl (hU h)))
  · exact Or.inr (Or.inl (hL h))

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
