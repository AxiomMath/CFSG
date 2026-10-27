module

public import CFSG.CGT.Timmesfeld75.Sec5Two

public section

namespace CFSG.CGT.Timmesfeld75

@[expose] def StepA1 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → secA T T₁ = ⊥

theorem step57_of_stepA1 (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) (hA : StepA1) :
    Step57 := by
  intro G _ T T₁ hyp x hx hx1 y hy hy1
  have : Finite G := hyp.finite
  have : IsSimpleGroup G := hyp.simple
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hyp.pair.wc
  have hA1 := hA G T T₁ hyp
  have hxA : x ∉ secA T T₁ := by rw [hA1]; simpa using hx1
  have hyA : y ∉ secA T T₁ := by rw [hA1]; simpa using hy1
  exact secA_transitive_hSub hTO hBW hyp.nonab hyp.pair hS hx hxA hy hyA

end CFSG.CGT.Timmesfeld75
