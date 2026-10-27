module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TS4Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TS4Map
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
public import Certificates.Certificate442352
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TS4Mod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec8t84FactS4_holds :
    Sec8T84FactS4 := by
  intro Y _ _ E H P F hE hEn hH hEH hEH' htr hP hF
  haveI := hEn
  obtain ⟨rr, C⟩ := sec8t84ts4_coord Certificates.certificate442349 hE hH hEH hEH' htr hP hF
  have S := Certificates.certificate442352
  have hM := sec8t84ts4_twoRes_iff S C
  exact ⟨sec8t84ts4_clause1 S C, sec8t84ts4_clause2 S C hM, sec8t84ts4_clause3 S C hM⟩

end CFSG.OddStandard.SmallF3.Omega
