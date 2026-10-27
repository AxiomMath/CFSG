module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2TData
public import CFSG.LocalAnalysis.OddStandard.ThmCO2D
public import CFSG.LocalAnalysis.OddStandard.ThmCO2CaseI
public import CFSG.LocalAnalysis.OddStandard.ThmCO2CaseII

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC

theorem o2Structure_of_hyps (hGor : Gor42) (hA8 : A8Fact) : O2Structure := by
  intro X _ _ hO hD T hT
  obtain ⟨e⟩ := hT
  obtain ⟨td⟩ := tData_of_equiv (T : Subgroup X) e
  by_cases hSn : (T : Subgroup X).Normal
  · exact caseI hO T e td hSn
  · rcases dClass hGor hO T td hD hSn with h | h
    · exact caseII hA8 hGor hO T td h hSn
    · exact caseII hA8 hGor hO T td.swap h hSn

end CFSG.OddStandard.ThmC.O2
