module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamLieOrd
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.I1420

@[expose] def LieDownChev : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.Open.IsKGroup Y →
    GLAPPrimeCore 3 Y = ⊥ → ∀ idx : TauCeti.ValidLieTypeIndex,
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ x : MulAut Y, orderOf x = 3 →
      ∀ J₁ : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ →
        (IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) →
          IsChevOfChar (lieIndexChar idx.1) (barOf 3 J₁ ⧸ Subgroup.center (barOf 3 J₁))

@[expose] def LieNoHatSix : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → CFSG.Open.IsKGroup Y →
    GLAPPrimeCore 3 Y = ⊥ →
    (∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
    ∀ x : MulAut Y, orderOf x = 3 →
      ∀ J₁ : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub x) J₁ →
        IsHatSix (barOf 3 J₁) → False

theorem gapFinalPumpupLie_of_residuals (hb : LieOrderBridge)
    (hOG : UniquenessMaximal.InputONGroup) (h1 : LieDownChev) (h2 : LieNoHatSix) :
    GapFinalPumpupLie := by
  intro Y _ _ hq hK hcore ⟨idx, hidx⟩ x hxo J₁ hJ₁ hty
  exfalso
  rcases hty with hON | hSix
  · have hChev := h1 Y hq hK hcore idx hidx x hxo J₁ hJ₁ (Or.inl hON)
    obtain ⟨d, -, ⟨f⟩⟩ := hChev
    obtain ⟨-, -, ⟨g⟩⟩ := hON
    have hcard : Nat.card (barOf 3 J₁ ⧸ Subgroup.center (barOf 3 J₁)) = orderON := by
      rw [Nat.card_congr g.toEquiv]
      exact hOG.2
    have hb' := hb d _ ⟨f⟩
    rw [hcard] at hb'
    exact GFR2Lie.lieOrderFormula_ne_onOrd d.2 (by rw [← hb']; unfold GFR2Lie.onOrd orderON; norm_num)
  · exact h2 Y hq hK hcore ⟨idx, hidx⟩ x hxo J₁ hJ₁ hSix

end CFSG.HardMathSupport.Solomon.Coordinator
