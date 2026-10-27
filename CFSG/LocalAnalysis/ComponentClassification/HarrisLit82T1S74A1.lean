module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ADefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74AConj

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

theorem a1_holds : A1 := by
  intro K _ _ hodd
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.OrthogonalPairs.IsFundamental.two_ne_zero_of_odd hodd
  refine ⟨iBar K, iBar_mul_self K, ?_, iBar_conj_tSeven K⟩
  rintro _ ⟨M, rfl⟩
  exact (commute_iBar_shortSeven K h2 M).eq

end CFSG.ComponentClassification.HarrisLit.T1.S74
