module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCyclicAux2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCyclicAux4

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem twPlaneCyclic_f4Six (K : Type) [Field K] [Finite K]
    (_hK : TwClass.f4Six.minQ ≤ Nat.card K) (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w)
    {p : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.f4Six.e) :
    (∀ g : ↥(TwClass.f4Six.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.f4Six.X₁ D)))) ∧
    (∀ g : ↥(TwClass.f4Six.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.f4Six.X₂ D)))) :=
  PlaneCyclic.planeCyclic_f4Six K D hp hord

theorem twPlaneCyclic_e6Six_X₂ (K : Type) [Field K] [Finite K]
    (_hK : TwClass.e6Six.minQ ≤ Nat.card K) (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w)
    {p : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e6Six.e) :
    ∀ g : ↥(TwClass.e6Six.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e6Six.X₂ D))) :=
  PlaneCyclic.planeCyclic_e6Six_X₂ K D hp hord

theorem twPlaneCyclic_e6Six (K : Type) [Field K] [Finite K]
    (hK : TwClass.e6Six.minQ ≤ Nat.card K) (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e6Six.e) :
    (∀ g : ↥(TwClass.e6Six.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e6Six.X₁ D)))) ∧
    (∀ g : ↥(TwClass.e6Six.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e6Six.X₂ D)))) :=
  ⟨PlaneCyclic.planeCyclic_e6Six_X₁ K D hp hord, twPlaneCyclic_e6Six_X₂ K hK D hp hp5 hord⟩

theorem twPlaneCyclic_e8Ten (K : Type) [Field K] [Finite K]
    (_hK : TwClass.e8Ten.minQ ≤ Nat.card K) (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)
    {p : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e8Ten.e) :
    (∀ g : ↥(TwClass.e8Ten.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Ten.X₁ D)))) ∧
    (∀ g : ↥(TwClass.e8Ten.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Ten.X₂ D)))) :=
  PlaneCyclic.planeCyclic_e8Ten K D hp hord

theorem twPlaneCyclic_e8Twelve (K : Type) [Field K] [Finite K]
    (_hK : TwClass.e8Twelve.minQ ≤ Nat.card K)
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e8Twelve.e) :
    (∀ g : ↥(TwClass.e8Twelve.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Twelve.X₁ D)))) ∧
    (∀ g : ↥(TwClass.e8Twelve.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Twelve.X₂ D)))) :=
  PlaneCyclic.planeCyclic_e8Twelve K D hp hp5 hord

theorem twPlaneCyclic (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = c.e) :
    (∀ g : ↥(c.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(c.X₁ D)))) ∧
    (∀ g : ↥(c.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(c.X₂ D)))) := by
  cases c
  · exact twPlaneCyclic_f4Six K hK D hp hp5 hord
  · exact twPlaneCyclic_e6Six K hK D hp hp5 hord
  · exact twPlaneCyclic_e8Ten K hK D hp hp5 hord
  · exact twPlaneCyclic_e8Twelve K hK D hp hp5 hord

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
