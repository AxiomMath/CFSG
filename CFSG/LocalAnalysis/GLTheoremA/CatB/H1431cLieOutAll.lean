module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutLin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutUni
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutSp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutExc
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutE6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutRee
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutType

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (characteristic_eq_two_iff)

theorem lieSOut_isSp68_of_isBIdx {i : TauCeti.CFSGIndex} (h : isBIdx 3 (2 ^ (3 * 1)) i) :
    isSp68 i := by
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B r q =>
      change r = 3 ∧ q.card = 2 ^ (3 * 1) at h
      obtain ⟨rfl, h⟩ := h
      show q.card = 8
      exact h.trans (by norm_num)
    | _ => exact h.elim
  | _ => exact h.elim

theorem lieSOut_isSp492_of_isBIdx {i : TauCeti.CFSGIndex} (h : isBIdx 2 (2 ^ (3 * 3)) i) :
    isSp492 i := by
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B r q =>
      change r = 2 ∧ q.card = 2 ^ (3 * 3) at h
      obtain ⟨rfl, h⟩ := h
      show q.card = 2 ^ 9
      exact h.trans (by norm_num)
    | _ => exact h.elim
  | _ => exact h.elim

section Assembly


theorem lieSOut_outAll {T : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}
    (hD : LieSOutType T tm tf tN) :
    TypeOuterAt T (isBIdx tm (2 ^ (3 * tf))) (fun d => FamA1 d ∨ FamA2 d ∨ FamAHigh d ∨
      FamTwA2 d ∨ FamTwAHigh d ∨ FamB d ∨ FamD4 d ∨ FamDHigh d ∨ FamTwD d ∨ FamE6 d ∨ FamTwE6 d ∨
      FamE7 d ∨ FamE8 d ∨ FamF4 d ∨ FamG2 d ∨ FamTriD4 d ∨ FamSz d ∨ FamReeF4 d ∨ FamTits d) := by
  refine (lieSOut_A1 hD).union ?_
  refine (lieSOut_A2 hD).union ?_
  refine (lieSOut_AHigh hD).union ?_
  refine (lieSOut_twA2 hD).union ?_
  refine (lieSOut_twAHigh hD).union ?_
  refine (lieSOut_B hD).union ?_
  refine (lieSOut_d4 hD).union ?_
  refine (lieSOut_dHigh hD).union ?_
  refine (lieSOut_twD hD).union ?_
  refine (lieSOut_e6 hD).union ?_
  refine (lieSOut_twE6 hD).union ?_
  refine (lieSOut_e7 hD).union ?_
  refine (lieSOut_e8 hD).union ?_
  refine (lieSOut_f4 hD).union ?_
  refine (lieSOut_g2 hD).union ?_
  refine (lieSOut_triD4 hD).union ?_
  refine (lieSOut_sz hD).union ?_
  exact (lieSOut_reeF4 hD).union (lieSOut_tits hD)

end Assembly

theorem lieSOut_holds :
    LieSOut := by
  intro S _ _ hs hnab d hc he α hα hα3
  have hα1 : α ≠ 1 := fun h => hα (h ▸ Subgroup.one_mem _)
  have hc' := characteristic_eq_two_iff.mp hc
  have hcov := famCover d hc'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact lieSOut_isSp68_of_isBIdx
      (lieSOut_outAll lieSOut_type_sp6two S hs hnab d hcov hc' he α hα ⟨hα3, hα1, h⟩)
  · exact lieSOut_isSp492_of_isBIdx
      (lieSOut_outAll lieSOut_type_sp48 S hs hnab d hcov hc' he α hα ⟨hα3, hα1, h⟩)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
