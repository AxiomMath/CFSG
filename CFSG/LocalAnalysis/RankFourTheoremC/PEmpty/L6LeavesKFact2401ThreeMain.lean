module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeAlt
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeLie

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kFact2401Three_holds
    : KFact2401Three := by
  intro A _ _ L E hL hE J hJ
  obtain ⟨Q, hQ⟩ := hE
  rcases hL with ⟨n, hn, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · exact Alt2401.le_of_alt hn e hQ hJ
  · rcases i with ⟨p, hp⟩ | ⟨m, hm⟩ | d | s
    · exact False.elim hi
    · exact False.elim hi
    · exact Bridge2401.le_of_glbCore_eq_top hQ hJ
        (Lie2401.glbCore_three_eq_top_of_rankTwoOdd L d hi e Q)
    · exact False.elim hi

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

end
