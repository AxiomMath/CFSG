module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CIField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem t263CI_lie_of_onLie {P : TauCeti.LieTypeIndex → Prop} {i : TauCeti.CFSGIndex} (h : onLie P i) :
    ∃ (d : TauCeti.LieTypeIndex) (hd : d.Valid), i = TauCeti.CFSGIndex.lie ⟨d, hd⟩ ∧ P d := by
  cases i with
  | cyclic _ _ => exact h.elim
  | alternating _ _ => exact h.elim
  | sporadic _ => exact h.elim
  | lie dv => exact ⟨dv.1, dv.2, rfl, h⟩

section Cells


theorem t263CaseIx_lin : T263CaseIx t263GLin := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi.1
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  have h28 := hi.2
  cases d with
  | A r q =>
    rcases r with _ | _ | r
    · simp [KD264Lie.outerPLayerExc] at h
    · exact absurd h.2 (by simpa [t263GL28, onLie] using h28)
    · simp [KD264Lie.outerPLayerExc] at h
  | _ => simp at hP

theorem t263CaseIx_uni : T263CaseIx t263GUni := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi.1
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  have h38 := hi.2
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    · simp [KD264Lie.outerPLayerExc] at h
    · simp [KD264Lie.outerPLayerExc] at h
    · exact absurd h.2 (by simpa [t263GU38, onLie] using h38)
    · simp [KD264Lie.outerPLayerExc] at h
  | _ => simp at hP

theorem t263CaseIx_symp : T263CaseIx t263GSymp := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  cases d <;> simp [KD264Lie.outerPLayerExc] at h hP

theorem t263CaseIx_orth : T263CaseIx t263GOrth := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  cases d <;> simp [KD264Lie.outerPLayerExc] at h hP

theorem t263CaseIx_twOrth : T263CaseIx t263GTwOrth := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  cases d <;> simp [KD264Lie.outerPLayerExc] at h hP

theorem t263CaseIx_e6 : T263CaseIx t263GE6 := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  cases d <;> simp [KD264Lie.outerPLayerExc] at h hP

theorem t263CaseIx_exc : T263CaseIx t263GExc := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  cases d <;> simp [KD264Lie.outerPLayerExc] at h hP

theorem t263CaseIx_td4 : T263CaseIx t263GTD4 := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  cases d <;> simp [KD264Lie.outerPLayerExc] at h hP
  rename_i q
  exact ⟨h, q, rfl⟩

theorem t263CaseIx_ree : T263CaseIx t263GRee := t263CaseIx_of_exc fun i hi => by
  obtain ⟨d, hd, rfl, hP⟩ := t263CI_lie_of_onLie hi
  refine ⟨d, hd, rfl, fun p h => ?_⟩
  cases d <;> simp [KD264Lie.outerPLayerExc] at h hP

end Cells

end CFSG.LocalAnalysis.GLTheoremA.T263

end
