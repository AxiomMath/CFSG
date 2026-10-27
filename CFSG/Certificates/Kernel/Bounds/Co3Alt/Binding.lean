module

public import CFSG.Certificates.Kernel.Bounds.Co3Alt.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Co3Alt

theorem rels_eq : TauCeti.Sporadic.co3Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.co3Presentation_transcribed]
  simp [rels]

theorem gens_eq : TauCeti.Sporadic.co3Presentation.generatorCount = 7 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co3Presentation_generatorNames]

theorem rels_T1_tau : KB.relsOk CFSG.KBData.Co3_T1v.R (nat_lit 24) T1.amap TauCeti.Sporadic.co3Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T1.rels_ok

theorem rels_T2_tau : KB.relsOk CFSG.KBData.Co3Alt_T2v.R (nat_lit 18) T2.amap TauCeti.Sporadic.co3Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T2.rels_ok

theorem rels_T3_tau : KB.relsOk CFSG.KBData.Co3Alt_T3v.R (nat_lit 12) T3.amap TauCeti.Sporadic.co3Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T3.rels_ok

end CFSG.KBRoute.Co3Alt

end
