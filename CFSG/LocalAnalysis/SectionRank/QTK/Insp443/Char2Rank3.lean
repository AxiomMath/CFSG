module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafAlt
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Split

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open CFSG.Quasithin

theorem forK_L42 :
    ForK (fun S _ => StatedClassicalModel S .PSL 4 2 1) := by
  refine ForK.mono (fun S _ h => ?_) Alt.forK_A8
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by simpa using hF
  exact ⟨((e.trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hF2 4)).trans
    (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hF2 4)).trans
    CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm⟩

theorem for_L42 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : For (fun S _ => StatedClassicalModel S .PSL 4 2 1) :=
  For.of_forK h37 h38 h39 forK_L42

theorem for_itemChar2Rank3_of (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hL5 : For (fun S _ => StatedClassicalModel S .PSL 5 2 1))
    (hSp6 : For (fun S _ => StatedClassicalModel S .PSp 3 2 1)) : For ItemChar2Rank3 := by
  intro G _ _ T M L B Tp VB K hHyp hP
  rcases hP with ⟨n, rfl | rfl, hm⟩ | hm
  · exact for_L42 h37 h38 h39 G T M L B Tp VB K hHyp hm
  · exact hL5 G T M L B Tp VB K hHyp hm
  · exact hSp6 G T M L B Tp VB K hHyp hm

end CFSG.SectionRank.QTK.Insp443

end
