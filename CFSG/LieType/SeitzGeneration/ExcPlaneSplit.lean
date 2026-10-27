module

public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies

public section

namespace CFSG.LieType.SeitzGeneration

open TauCeti

@[expose] def ExcPlaneF4Low : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .F4 q ∧ p ∣ q.card ^ 2 - 1

@[expose] def ExcPlaneF4Rest : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .F4 q ∧ ¬ p ∣ q.card ^ 2 - 1

theorem excPlaneF4_of_parts (h₁ : ExcPlaneF4Low) (h₂ : ExcPlaneF4Rest) : ExcPlaneF4 := by
  refine ExcParabolicPlaneOn.of_cover (fun d p _ _ hS => ?_) h₁ h₂
  obtain ⟨q, rfl⟩ := hS
  by_cases h : p ∣ q.card ^ 2 - 1
  exacts [Or.inl ⟨q, rfl, h⟩, Or.inr ⟨q, rfl, h⟩]

@[expose] def ExcPlaneE6Low : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E6 q ∧ p ∣ q.card ^ 2 - 1

@[expose] def ExcPlaneE6E3 : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E6 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    p ∣ q.card ^ 2 + q.card + 1

@[expose] def ExcPlaneE6Rest : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E6 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    ¬ p ∣ q.card ^ 2 + q.card + 1

theorem excPlaneE6_of_parts (h₁ : ExcPlaneE6Low) (h₂ : ExcPlaneE6E3) (h₃ : ExcPlaneE6Rest) :
    ExcPlaneE6 := by
  refine ExcParabolicPlaneOn.of_cover (fun d p _ _ hS => ?_) h₁
    (ExcParabolicPlaneOn.of_cover (S := fun d p => ∃ q : PrimePower, d = .E6 q ∧
      ¬ p ∣ q.card ^ 2 - 1) (fun d p _ _ hS => ?_) h₂ h₃)
  · obtain ⟨q, rfl⟩ := hS
    by_cases h : p ∣ q.card ^ 2 - 1
    exacts [Or.inl ⟨q, rfl, h⟩, Or.inr ⟨q, rfl, h⟩]
  · obtain ⟨q, rfl, h⟩ := hS
    by_cases h' : p ∣ q.card ^ 2 + q.card + 1
    exacts [Or.inl ⟨q, rfl, h, h'⟩, Or.inr ⟨q, rfl, h, h'⟩]

@[expose] def ExcPlaneE7Low : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E7 q ∧ p ∣ q.card ^ 2 - 1

@[expose] def ExcPlaneE7E3 : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E7 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    p ∣ q.card ^ 2 + q.card + 1

@[expose] def ExcPlaneE7E6 : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E7 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    p ∣ q.card ^ 2 - q.card + 1

@[expose] def ExcPlaneE7Rest : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E7 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    ¬ p ∣ q.card ^ 2 + q.card + 1 ∧ ¬ p ∣ q.card ^ 2 - q.card + 1

theorem excPlaneE7_of_parts (h₁ : ExcPlaneE7Low) (h₂ : ExcPlaneE7E3) (h₃ : ExcPlaneE7E6)
    (h₄ : ExcPlaneE7Rest) : ExcPlaneE7 := by
  refine ExcParabolicPlaneOn.of_cover (fun d p _ _ hS => ?_) h₁
    (ExcParabolicPlaneOn.of_cover (S := fun d p => ∃ q : PrimePower, d = .E7 q ∧
      ¬ p ∣ q.card ^ 2 - 1) (fun d p _ _ hS => ?_) h₂
      (ExcParabolicPlaneOn.of_cover (S := fun d p => ∃ q : PrimePower, d = .E7 q ∧
        ¬ p ∣ q.card ^ 2 - 1 ∧ ¬ p ∣ q.card ^ 2 + q.card + 1) (fun d p _ _ hS => ?_) h₃ h₄))
  · obtain ⟨q, rfl⟩ := hS
    by_cases h : p ∣ q.card ^ 2 - 1
    exacts [Or.inl ⟨q, rfl, h⟩, Or.inr ⟨q, rfl, h⟩]
  · obtain ⟨q, rfl, h⟩ := hS
    by_cases h' : p ∣ q.card ^ 2 + q.card + 1
    exacts [Or.inl ⟨q, rfl, h, h'⟩, Or.inr ⟨q, rfl, h, h'⟩]
  · obtain ⟨q, rfl, h, h'⟩ := hS
    by_cases h'' : p ∣ q.card ^ 2 - q.card + 1
    exacts [Or.inl ⟨q, rfl, h, h''⟩, Or.inr ⟨q, rfl, h, h', h''⟩]

@[expose] def ExcPlaneE8Low : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E8 q ∧ p ∣ q.card ^ 2 - 1

@[expose] def ExcPlaneE8E3 : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E8 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    p ∣ q.card ^ 2 + q.card + 1

@[expose] def ExcPlaneE8E4 : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E8 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    p ∣ q.card ^ 2 + 1

@[expose] def ExcPlaneE8E6 : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E8 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    p ∣ q.card ^ 2 - q.card + 1

@[expose] def ExcPlaneE8Rest : Prop :=
  ExcParabolicPlaneOn fun d p => ∃ q : PrimePower, d = .E8 q ∧ ¬ p ∣ q.card ^ 2 - 1 ∧
    ¬ p ∣ q.card ^ 2 + q.card + 1 ∧ ¬ p ∣ q.card ^ 2 + 1 ∧ ¬ p ∣ q.card ^ 2 - q.card + 1

theorem excPlaneE8_of_parts (h₁ : ExcPlaneE8Low) (h₂ : ExcPlaneE8E3) (h₃ : ExcPlaneE8E4)
    (h₄ : ExcPlaneE8E6) (h₅ : ExcPlaneE8Rest) : ExcPlaneE8 := by
  refine ExcParabolicPlaneOn.of_cover (fun d p _ _ hS => ?_) h₁
    (ExcParabolicPlaneOn.of_cover (S := fun d p => ∃ q : PrimePower, d = .E8 q ∧
      ¬ p ∣ q.card ^ 2 - 1) (fun d p _ _ hS => ?_) h₂
      (ExcParabolicPlaneOn.of_cover (S := fun d p => ∃ q : PrimePower, d = .E8 q ∧
        ¬ p ∣ q.card ^ 2 - 1 ∧ ¬ p ∣ q.card ^ 2 + q.card + 1) (fun d p _ _ hS => ?_) h₃
        (ExcParabolicPlaneOn.of_cover (S := fun d p => ∃ q : PrimePower, d = .E8 q ∧
          ¬ p ∣ q.card ^ 2 - 1 ∧ ¬ p ∣ q.card ^ 2 + q.card + 1 ∧ ¬ p ∣ q.card ^ 2 + 1)
          (fun d p _ _ hS => ?_) h₄ h₅)))
  · obtain ⟨q, rfl⟩ := hS
    by_cases h : p ∣ q.card ^ 2 - 1
    exacts [Or.inl ⟨q, rfl, h⟩, Or.inr ⟨q, rfl, h⟩]
  · obtain ⟨q, rfl, h⟩ := hS
    by_cases h' : p ∣ q.card ^ 2 + q.card + 1
    exacts [Or.inl ⟨q, rfl, h, h'⟩, Or.inr ⟨q, rfl, h, h'⟩]
  · obtain ⟨q, rfl, h, h'⟩ := hS
    by_cases h'' : p ∣ q.card ^ 2 + 1
    exacts [Or.inl ⟨q, rfl, h, h''⟩, Or.inr ⟨q, rfl, h, h', h''⟩]
  · obtain ⟨q, rfl, h, h', h''⟩ := hS
    by_cases h''' : p ∣ q.card ^ 2 - q.card + 1
    exacts [Or.inl ⟨q, rfl, h, h'''⟩, Or.inr ⟨q, rfl, h, h', h'', h'''⟩]

end CFSG.LieType.SeitzGeneration
