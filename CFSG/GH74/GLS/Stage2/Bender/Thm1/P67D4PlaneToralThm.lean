module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ApMain

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4PlaneToral_thm : D4PlaneToral := by
  refine fun p f hp hp2 hp3 hf K _ _ hK σ hσ hq E hE hEcard _ => ?_
  rcases d4Minus_plane_dichotomy hp hp2 hp3 hf hq K hK σ hσ E hE hEcard with hT | ⟨β, hfr⟩
  · obtain ⟨β, hgood⟩ := ap_plane_good hp hp2 hp3 hf hq hK hσ hE hEcard hT
    exact ⟨β, Or.inr hgood⟩
  · exact ⟨β, Or.inl hfr⟩

theorem g2d4InnerPlaneGen_thm : G2D4InnerPlaneGen :=
  d4PlaneToral_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm1
