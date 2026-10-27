module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutA6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutLin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutUni
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutSp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutExc
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutE6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutTriD4Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutD4Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutRee
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Dickson.Sec6
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (characteristic_eq_two_iff)

theorem lieSOut_isSp48_of_isBIdx {i : TauCeti.CFSGIndex} (h : isBIdx 2 (2 ^ (3 * 1)) i) :
    S8.L84.isSp48 i := by
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B r q =>
      change r = 2 ∧ q.card = 2 ^ (3 * 1) at h
      obtain ⟨rfl, h⟩ := h
      show q.card = 8
      exact h.trans (by norm_num)
    | _ => exact h.elim
  | _ => exact h.elim


theorem lieSOutW_outAll {T : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}
    (hD : LieSOutTypeW T tm tf tN) :
    TypeOuterAt T (isBIdx tm (2 ^ (3 * tf))) (fun d => FamA1 d ∨ FamA2 d ∨ FamAHigh d ∨
      FamTwA2 d ∨ FamTwAHigh d ∨ FamB d ∨ FamD4 d ∨ FamDHigh d ∨ FamTwD d ∨ FamE6 d ∨ FamTwE6 d ∨
      FamE7 d ∨ FamE8 d ∨ FamF4 d ∨ FamG2 d ∨ FamTriD4 d ∨ FamSz d ∨ FamReeF4 d ∨ FamTits d) := by
  refine (lieSOut_A1W hD).union ?_
  refine (lieSOut_A2W hD).union ?_
  refine (lieSOut_AHighW hD).union ?_
  refine (lieSOut_twA2W hD).union ?_
  refine (lieSOut_twAHighW hD).union ?_
  refine (lieSOut_BW hD).union ?_
  refine (lieSOut_d4W hD).union ?_
  refine (lieSOut_dHighW hD).union ?_
  refine (lieSOut_twDW hD).union ?_
  refine (lieSOut_e6W hD).union ?_
  refine (lieSOut_twE6W hD).union ?_
  refine (lieSOut_e7W hD).union ?_
  refine (lieSOut_e8W hD).union ?_
  refine (lieSOut_f4W hD).union ?_
  refine (lieSOut_g2W hD).union ?_
  refine (lieSOut_triD4W hD).union ?_
  refine (lieSOut_szW hD).union ?_
  exact (lieSOut_reeF4W hD).union lieSOut_tits_of_inner

theorem lieSOutA6_holds :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ α : MulAut S, α ∉ innAutDerived S → α ^ 3 = 1 → CompOfType S α S8.isA6 →
          S8.L84.isSp48 (.lie d) := by
  intro S _ _ hs hnab d hc he α hα hα3 h
  have hα1 : α ≠ 1 := fun h => hα (h ▸ Subgroup.one_mem _)
  have hc' := characteristic_eq_two_iff.mp hc
  exact lieSOut_isSp48_of_isBIdx
    (lieSOutW_outAll lieSOutTypeW_a6 S hs hnab d (famCover d hc') hc' he α hα ⟨hα3, hα1, h⟩)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
