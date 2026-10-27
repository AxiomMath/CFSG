module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFrontier
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Reduction

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.AGLEmbedding TauCeti

@[expose] def CoopersteinNoIrrFFE6 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid), q.p = 2 →
    NoIrrFFOffender (CFSGIndex.lie ⟨.E6 q, hv⟩).Group

@[expose] def CoopersteinNoIrrFFTwistedE6 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), q.p = 2 →
    NoIrrFFOffender (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group

@[expose] def CoopersteinNoIrrFFE7 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid), q.p = 2 →
    NoIrrFFOffender (CFSGIndex.lie ⟨.E7 q, hv⟩).Group


theorem coopersteinNoFFExceptionalRestNoE8_of_families (hE6 : CoopersteinNoIrrFFE6)
    (hTE6 : CoopersteinNoIrrFFTwistedE6) (hE7 : CoopersteinNoIrrFFE7) :
    CoopersteinNoFFExceptionalRestNoE8 := by
  intro d hd hc hq h8
  obtain ⟨d, hv⟩ := d
  have hcl : IsClassicalOrG2Index d → False := fun hidx =>
    hc (Or.inl ⟨⟨d, hv⟩, hidx, ⟨MulEquiv.refl _⟩⟩)
  cases d with
  | A r q => exact (hcl (by simpa [IsClassicalOrG2Index] using hd)).elim
  | twistedA r q => exact (hcl (by simpa [IsClassicalOrG2Index] using hd)).elim
  | B r q => exact (hcl (by simpa [IsClassicalOrG2Index] using hd)).elim
  | C r q =>
    have h2 : q.p = 2 := by simpa using hd
    exact (((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).2 h2).elim
  | D r q => exact (hcl (by simpa [IsClassicalOrG2Index] using hd)).elim
  | twistedD r q => exact (hcl (by simpa [IsClassicalOrG2Index] using hd)).elim
  | G2 q => exact (hcl (by simpa [IsClassicalOrG2Index] using hd)).elim
  | F4 q =>
    exact noFFModule_of_noIrrFFOffender (F4Exc.noIrrFFOffender_F4 q hv (by simpa using hd))
  | E6 q => exact noFFModule_of_noIrrFFOffender (hE6 q hv (by simpa using hd))
  | twistedE6 q => exact noFFModule_of_noIrrFFOffender (hTE6 q hv (by simpa using hd))
  | E7 q => exact noFFModule_of_noIrrFFOffender (hE7 q hv (by simpa using hd))
  | E8 q => exact (h8 (by simp [IsE8Index])).elim
  | trialityD4 q => exact (hq (by simpa [IsSQTKExceptionalTwoIndex] using hd)).elim
  | suzuki m => exact (hq (by simp [IsSQTKExceptionalTwoIndex])).elim
  | reeF4 m => exact (hq (by simp [IsSQTKExceptionalTwoIndex])).elim
  | tits => exact (hq (by simp [IsSQTKExceptionalTwoIndex])).elim
  | reeG2 m => exact absurd hd (by simp)

end CFSG.HardMathSupport.Cooperstein.Coordinator
