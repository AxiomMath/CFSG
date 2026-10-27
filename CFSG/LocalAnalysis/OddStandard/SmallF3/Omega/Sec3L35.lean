module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma35_of_34c (h : Asc82Lemma34c) : Asc82Lemma35 := by
  intro G _ _ t L hS x X y K u hP hu huy J hJ
  have hy : orderOf y = 2 := hP.involution_y
  have hcomm : u * y = y * u :=
    (Subgroup.mem_centralizer_iff.1 huy y (Set.mem_singleton y)).symm
  obtain ⟨K', hK', hle⟩ := hS.lBalance u y hu hy hcomm J hJ.1
  exact h G t L hS x X y K hP K' hK' (hS.a2 u y hu hy hcomm J K' hJ.1 hK' hle hJ.2)

end CFSG.OddStandard.SmallF3.Omega
