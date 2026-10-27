module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreX
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem kd264CoreS_holds (hI : KD264LieInputs) {p : ℕ} (hPL : KD264PL p) (hBS : KD264BS p)
    (hAmb : KD264Amb p) (hY1 : KD264CaseY1) (hY2 : KD264CaseY2) : KD264CoreS p := by
  intro d _ A m c h
  by_cases hX : p = 3 ∧ ov2Idx d.1
  · exact kd264CoreGoal_of_caseX hI d A m c h hX
  · obtain rfl | rfl : c = 1 ∨ c = 2 := by have := h.one_le_c; have := h.c_le_two; omega
    · exact kd264CoreGoal_of_c_eq_one hI hPL hBS hAmb hY1 hY2 d A m h hX
    · exact kd264CoreGoal_of_c_eq_two hI hPL d A m h hX

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
