module

public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyThree

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Fi23Alt

theorem rels_eq : TauCeti.Sporadic.fi23Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.fi23Presentation_transcribed]
  simp [rels]

theorem gens_eq : TauCeti.Sporadic.fi23Presentation.generatorCount = 10 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.fi23Presentation_generatorNames]

theorem rels_T1_tau : KB.relsOk CFSG.KBData.Fi23_T1v.R (nat_lit 57) T1.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T1.rels_ok

theorem rels_T2_tau : KB.relsOk CFSG.KBData.Fi23Alt_T2v.R (nat_lit 47) T2.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T2.rels_ok

theorem rels_T3_tau : KB.relsOk CFSG.KBData.Fi23Alt_T3v.R (nat_lit 37) T3.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T3.rels_ok

theorem rels_T4_tau : KB.relsOk CFSG.KBData.Fi23Alt_T4v.R (nat_lit 28) T4.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T4.rels_ok

theorem rels_T5_tau : KB.relsOk CFSG.KBData.Fi23Alt_T5v.R (nat_lit 21) T5.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T5.rels_ok

theorem rels_T6_tau : KB.relsOk CFSG.KBData.Fi23Alt_T6v.R (nat_lit 15) T6.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T6.rels_ok

theorem rels_T7_tau : KB.relsOk CFSG.KBData.Fi23Alt_T7v.R (nat_lit 10) T7.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T7.rels_ok

theorem rels_T8_tau : KB.relsOk CFSG.KBData.Fi23Alt_T8v.R (nat_lit 6) T8.amap TauCeti.Sporadic.fi23Presentation.relatorLetters = true := by
  rw [rels_eq]; exact T8.rels_ok

end CFSG.KBRoute.Fi23Alt

end
