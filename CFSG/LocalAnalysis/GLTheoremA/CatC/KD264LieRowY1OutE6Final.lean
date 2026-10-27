module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutE6Tw
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutFinal

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section Certificates

theorem kd264Y1OutE6_holds : KD264Y1OutE6 := by
  intro d hfin hP _ _ _ hpR a ha ha3
  obtain ⟨e, hv⟩ := d
  rcases hP with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact kd264Y1OutE6_untwisted q hv hpR ha ha3
  · exact kd264Y1OutE6_twisted q hv hpR ha

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
