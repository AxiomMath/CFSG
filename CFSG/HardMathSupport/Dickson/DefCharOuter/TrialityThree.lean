module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def TrialityThreeOuter : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) → q.p = 3 →
    ∀ β : MulAut S, β ^ 3 = 1 → (∀ a : S, MulAut.conj a ≠ β) →
      PerfectInLayer β ∨ CFSG.Open.GLAPPrimeCoreOf 3 (fixSubgroup β) = ⊥

theorem lieDefCharOuter_trialityD4_three (h2 : TrialityThreeOuter) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩)
    {p : ℕ} (hpc : p = q.p) (hp3 : p = 3)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β ∨ CFSG.Open.GLAPPrimeCoreOf p (fixSubgroup β) = ⊥ := by
  subst hp3
  exact h2 q hv S hnc e hpc.symm β hβ hout

end CFSG.HardMathSupport.Dickson.DefCharOuter
