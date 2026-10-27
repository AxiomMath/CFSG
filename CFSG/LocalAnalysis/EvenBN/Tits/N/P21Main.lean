module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Hyp5
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Concl
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LMain

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.LocalAnalysis.EvenBN.Tits.I21L

section Main

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}



theorem step21_holds : Step21 := by
  intro G _ _ d z₀ h49 hd hz h09 h19 h19b h20
  obtain ⟨hW, t, u, x, h, htα, hxα, hX, H⟩ := p21_hyp h49 hd hz h09 h19 h19b h20
  obtain ⟨hdich, hP⟩ := thm_10_7 H
  exact p21_concl h09 hW htα hX hdich hP

end Main

end CFSG.LocalAnalysis.EvenBN.Tits.N
