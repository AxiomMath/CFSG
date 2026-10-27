module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open TauCeti

@[expose] def HasDiagOuterThree (X : Type) [Group X] : Prop :=
  ∃ α : MulAut X, ∀ k : ℕ, α ^ (2 ^ k) ∉ (MulAut.conj : X →* MulAut X).range

@[expose] def IsLinUniIndex3 : LieTypeIndex → Prop
  | .A r q => 3 ∣ r + 1 ∧ 3 ∣ q.card - 1
  | .twistedA r q => 3 ∣ r + 1 ∧ 3 ∣ q.card + 1
  | _ => False

@[expose] def DiagOuterLinUni : Prop :=
  ∀ d : ValidLieTypeIndex, IsLinUniIndex3 d.1 → HasDiagOuterThree (CFSGIndex.lie d).Group

@[expose] def DiagOuterE6 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid), 3 ∣ q.card - 1 →
    HasDiagOuterThree (CFSGIndex.lie ⟨.E6 q, hv⟩).Group

@[expose] def DiagOuterTwistedE6 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), 3 ∣ q.card + 1 →
    HasDiagOuterThree (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group

@[expose] def WeakGenU43 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 3 →
    CoverWeakGen (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group 3

@[expose] def WeakGenO73 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.card = 3 →
    CoverWeakGen (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group 3

@[expose] def WeakGenG23 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.card = 3 →
    CoverWeakGen (CFSGIndex.lie ⟨.G2 q, hv⟩).Group 3

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
