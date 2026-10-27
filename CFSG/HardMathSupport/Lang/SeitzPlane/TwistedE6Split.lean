module

public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.LieType.SeitzGeneration TauCeti

@[expose] def ExcPlaneTwistedE6Low : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .twistedE6 q ∧ p ∣ q.card ^ 2 - 1

@[expose] def ExcPlaneTwistedE6Six : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .twistedE6 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    p ∣ q.card ^ 2 - q.card + 1

@[expose] def ExcPlaneTwistedE6Rest : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .twistedE6 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    ¬ p ∣ q.card ^ 2 - q.card + 1

theorem excPlaneTwistedE6_of_parts (h₁ : ExcPlaneTwistedE6Low) (h₂ : ExcPlaneTwistedE6Six)
    (h₃ : ExcPlaneTwistedE6Rest) : ExcPlaneTwistedE6 := by
  refine ExcParabolicPlaneOn.of_cover (fun d p _ _ hS => ?_) h₁
    (ExcParabolicPlaneOn.of_cover (S := fun d p => ∃ q : PrimePower, d = .twistedE6 q ∧
      ¬ p ∣ q.card ^ 2 - 1) (fun d p _ _ hS => ?_) h₂ h₃)
  · obtain ⟨q, rfl⟩ := hS
    by_cases h : p ∣ q.card ^ 2 - 1
    exacts [Or.inl ⟨q, rfl, h⟩, Or.inr ⟨q, rfl, h⟩]
  · obtain ⟨q, rfl, h⟩ := hS
    by_cases h' : p ∣ q.card ^ 2 - q.card + 1
    exacts [Or.inl ⟨q, rfl, h, h'⟩, Or.inr ⟨q, rfl, h, h'⟩]

end CFSG.HardMathSupport.Lang.SeitzPlane
