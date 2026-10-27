module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcD4Triality

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a

@[expose] def NonD4LieContraOnF4TwoOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q : ℕ),
    I1433Cfg K Q₁ Q J t q →
    ∀ (r : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 r).Valid), r.p = 2 →
      Odd r.exponent →
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie ⟨.F4 r, hv⟩).Group) →
      ¬ IsD4Simple (↥K ⧸ Subgroup.center ↥K) → False

set_option linter.unusedSectionVars false


theorem nonD4LieContraOnExcSmall_of_residual (h : NonD4LieContraOnF4TwoOdd) :
    NonD4LieContraOnExcSmall := by
  intro X _ _ K Q₁ Q J t q p c hp hp3 idx hfam hs hchev he hnD4
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A n r => simp [ExcSmallIndex] at hs
  | twistedA n r => simp [ExcSmallIndex] at hs
  | B n r => simp [ExcSmallIndex] at hs
  | C n r => simp [ExcSmallIndex] at hs
  | D n r => simp [ExcSmallIndex] at hs
  | twistedD n r => simp [ExcSmallIndex] at hs
  | suzuki m => simp [ExcSmallIndex] at hs
  | reeG2 m => simp [ExcSmallIndex] at hs
  | reeF4 m => simp [ExcSmallIndex] at hs
  | tits => simp [ExcSmallIndex] at hs
  | E6 r => simp [ExcSmallIndex] at hs
  | E7 r => simp [ExcSmallIndex] at hs
  | E8 r => simp [ExcSmallIndex] at hs
  | G2 r =>
    have hr : r.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hchev
    exact false_of_i1433Cfg_G2 c r hv (hr ▸ hp3) he
  | trialityD4 r =>
    have hr : r.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hchev
    exact false_of_i1433Cfg_trialityD4 c r hv (hr ▸ hp3) he
  | F4 r => exact h X K Q₁ Q J t q c r hv hs.1 hs.2 he hnD4
  | twistedE6 r => simp [ExcSmallIndex] at hs

theorem nonD4LieContraOn_exceptional_of_residual (h : NonD4LieContraOnF4TwoOdd) :
    NonD4LieContraOn .exceptional :=
  nonD4LieContraOn_exceptional_of_small (nonD4LieContraOnExcSmall_of_residual h)

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
