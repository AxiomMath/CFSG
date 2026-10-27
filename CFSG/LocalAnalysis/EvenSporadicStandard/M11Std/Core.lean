module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Case01c

public section

namespace CFSG.EvenSporadicStandard.M11Std

variable {G : Type} [Group G] [Finite G]

theorem Setting.false' (H : Setting G) : False := by
  rcases H.cases with ⟨h1, -, hn⟩ | ⟨h1, h2, hn⟩ | ⟨h1, -, hn⟩
  · exact H.false_case11 h1 hn
  · exact H.false_case10 h2 hn
  · exact H.false_case01 h1 hn

end CFSG.EvenSporadicStandard.M11Std
