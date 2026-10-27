module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdQuat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdChar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.GS82PumpInputs (OddLieCharUnique)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)

theorem asc82StandardInput_of_rk2 (hRk2 : Asc82StandardInputRk2)
    (hCIT : ClassicalInvolutionTheoremModels) (hGLS : GLS3OddLieAutComponentsInput)
    (hC : OddLieCharUnique) (hM11 : Nat.card NativeSporadic.M11 = 7920)
    (hM12 : Nat.card NativeSporadic.M12 = 95040) : Asc82StandardInput := by
  intro G _ _ hs hK hn hA1 hA2 hLC X hX hXF hS
  haveI := hs
  by_cases hrk : 2 ≤ pRank 2 ↥(centralizer (X : Set G))
  · exact hRk2 G hs hK hn hA1 hA2 hLC X hX hXF hrk
  obtain ⟨L, hLF, hLC'⟩ := hLC
  rcases s7f_oddLie_or_mathieu hCIT hX hXF hrk hS with ho | hm | hm
  · exact s7f_chev3_of_oddLieType hGLS hC ⟨L, hLF, hLC'⟩ ho
  · exact absurd hm (s7f_not_M11 hM11 hLF)
  · exact absurd hm (s7f_not_M12 hM12 hLF)

end CFSG.OddStandard.SmallF3.Omega
