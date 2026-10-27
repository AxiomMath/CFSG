module

public import CFSG.LieType.SeitzGeneration.Dispatch

public section

namespace CFSG.LieType.SeitzGeneration

@[expose] def CentralPrimeFree (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .A m q => ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1)
  | .twistedA m q => ¬ (p ∣ q.card + 1 ∧ p ∣ m + 1)
  | _ => True

@[expose] def SeitzInnerClassicalAb : Prop :=
  SeitzPlanes fun d p E =>
    InnerPlane d p E ∧ 5 ≤ p ∧ IsClassicalIndex d.1 ∧ CentralPrimeFree p d.1

@[expose] def SeitzInnerClassicalNonab : Prop :=
  SeitzPlanes fun d p E =>
    InnerPlane d p E ∧ 5 ≤ p ∧ IsClassicalIndex d.1 ∧ ¬ CentralPrimeFree p d.1

theorem seitzInnerClassicalFive_of_lift (h₁ : SeitzInnerClassicalAb)
    (h₂ : SeitzInnerClassicalNonab) : SeitzInnerClassicalFive :=
  SeitzPlanes.of_cover (fun d p _ _ E ⟨hE, h5, hc⟩ => by
    by_cases hf : CentralPrimeFree p d.1
    · exact Or.inl ⟨hE, h5, hc, hf⟩
    · exact Or.inr ⟨hE, h5, hc, hf⟩) h₁ h₂

@[expose] def IsLinearIndex (d : TauCeti.LieTypeIndex) : Prop := ∃ (m : ℕ) (q : TauCeti.PrimePower),
  d = .A m q

@[expose] def IsUnitaryIndex' (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), d = .twistedA m q

@[expose] def IsSymplecticIndex (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d = .B 2 q) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .B r q ∧ 3 ≤ r ∧ q.p = 2) ∨
    ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .C r q

@[expose] def IsOrthogonalIndex (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .B r q ∧ 3 ≤ r ∧ q.p ≠ 2) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .D r q) ∨
    ∃ (r : ℕ) (q : TauCeti.PrimePower), d = .twistedD r q

theorem isClassicalIndex_iff {d : TauCeti.LieTypeIndex} (hd : d.InStandardRange) :
    IsClassicalIndex d ↔ IsLinearIndex d ∨ IsUnitaryIndex' d ∨ IsSymplecticIndex d ∨
      IsOrthogonalIndex d := by
  constructor
  · intro h
    cases d with
    | A m q => exact Or.inl ⟨m, q, rfl⟩
    | twistedA m q => exact Or.inr (Or.inl ⟨m, q, rfl⟩)
    | B r q =>
      have hr : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 hd).1
      by_cases h2 : r = 2
      · subst h2
        exact Or.inr (Or.inr (Or.inl (Or.inl ⟨q, rfl⟩)))
      · by_cases hq : q.p = 2
        · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨r, q, rfl, by omega, hq⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl, by omega, hq⟩)))
    | C r q => exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨r, q, rfl⟩))))
    | D r q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))))
    | twistedD r q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, q, rfl⟩))))
    | E6 q => exact h.elim
    | E7 q => exact h.elim
    | E8 q => exact h.elim
    | F4 q => exact h.elim
    | G2 q => exact h.elim
    | twistedE6 q => exact h.elim
    | trialityD4 q => exact h.elim
    | suzuki m => exact h.elim
    | reeG2 m => exact h.elim
    | reeF4 m => exact h.elim
    | tits => exact h.elim
  · rintro (⟨m, q, rfl⟩ | ⟨m, q, rfl⟩ | (⟨q, rfl⟩ | ⟨r, q, rfl, -⟩ | ⟨r, q, rfl⟩) |
      (⟨r, q, rfl, -⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩)) <;> trivial

end CFSG.LieType.SeitzGeneration
