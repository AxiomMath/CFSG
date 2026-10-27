module

public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def GapFinalPumpupSpor (name : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.Open.IsKGroup Y →
    GLAPPrimeCore 3 Y = ⊥ →
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
    ∀ x : MulAut Y, orderOf x = 3 →
      ∀ J₁ : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ →
        (IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) →
          IsHatON Y ∨ IsHatSix Y ∨ IsMJRType Y

@[expose] def GapFinalPumpupLie : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.Open.IsKGroup Y →
    GLAPPrimeCore 3 Y = ⊥ →
    (∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
    ∀ x : MulAut Y, orderOf x = 3 →
      ∀ J₁ : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ →
        (IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) →
          IsHatON Y ∨ IsHatSix Y ∨ IsMJRType Y

end CFSG.HardMathSupport.Solomon.Coordinator
