module

public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open CFSG.Blueprint.NativeSporadic

theorem mulAut_inner_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ φ : MulAut Y, ∃ g, φ = MulAut.conj g) (φ : MulAut X) : ∃ g, φ = MulAut.conj g := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e φ)
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun ψ : MulAut Y => ψ (e x)) hg
  apply e.injective
  simpa [MulAut.congr_apply] using h1

@[expose] def RuAutInner : Prop := ∀ φ : MulAut (Carrier .Ru), ∃ g, φ = MulAut.conj g

theorem ruAutInner :
    RuAutInner := by
  have e : Carrier .Ru ≃* CFSG.Sporadic.RuSchreier.ruP := CFSG.Sporadic.RuSchreier.ruEquivP
  exact mulAut_inner_of_mulEquiv e CFSG.Sporadic.RuSchreier.mulAut_inner

end CFSG.EvenSporadicStandard.Induction.Balance
