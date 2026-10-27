module

public import CFSG.Certificates.Kernel.Bounds.ON.Route
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan
public import Std.Tactic.BVDecide.Normalize.Bool

open CFSG.Certificates

public section

namespace CFSG.KBRoute.ON

theorem rels_eq : TauCeti.Sporadic.onanPresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.onanPresentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem gens_eq : TauCeti.Sporadic.onanPresentation.generatorCount = 7 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.onanPresentation_generatorNames]

theorem rels_T1_tau : KB.relsOk CFSG.KBData.ON_T1v.R (nat_lit 29) T1.amap TauCeti.Sporadic.onanPresentation.relatorLetters = true := by
  rw [rels_eq]; exact T1.rels_ok

theorem rels_T2_tau : KB.relsOk CFSG.KBData.ON_T2v.R (nat_lit 22) T2.amap TauCeti.Sporadic.onanPresentation.relatorLetters = true := by
  rw [rels_eq]; exact T2.rels_ok

theorem rels_T3_tau : KB.relsOk CFSG.KBData.ON_T3v.R (nat_lit 15) T3.amap TauCeti.Sporadic.onanPresentation.relatorLetters = true := by
  rw [rels_eq]; exact T3.rels_ok

end CFSG.KBRoute.ON

end
