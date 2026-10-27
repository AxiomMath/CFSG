module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib.GroupTheory.FreeGroup.Reduce

public section

namespace CFSG.Literature.ParrottTits

open CFSG.CosetTable

abbrev r₁ : FreeGroup (Fin 10) := FreeGroup.of 0

abbrev r₈ : FreeGroup (Fin 10) := FreeGroup.of 1

abbrev s₁ : FreeGroup (Fin 10) := FreeGroup.of 2

abbrev s₂ : FreeGroup (Fin 10) := FreeGroup.of 3

abbrev s₃ : FreeGroup (Fin 10) := FreeGroup.of 4

abbrev s₄ : FreeGroup (Fin 10) := FreeGroup.of 5

abbrev s₅ : FreeGroup (Fin 10) := FreeGroup.of 6

abbrev s₆ : FreeGroup (Fin 10) := FreeGroup.of 7

abbrev s₇ : FreeGroup (Fin 10) := FreeGroup.of 8

abbrev s₈ : FreeGroup (Fin 10) := FreeGroup.of 9

@[expose] def pcomm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

abbrev r₃ : FreeGroup (Fin 10) := s₁ * s₂ * s₃ ^ 2

abbrev r₅ : FreeGroup (Fin 10) := s₁ * s₅ ^ 2

abbrev r₇ : FreeGroup (Fin 10) := r₃ * s₃ * s₅ * s₇

@[expose] def parrottRelations : List (FreeGroup (Fin 10) × FreeGroup (Fin 10)) :=
  [(r₁ ^ 2, 1), (r₈ ^ 2, 1), (s₁ ^ 2, 1), (s₂ ^ 2, 1), (s₄ ^ 2, 1), (s₆ ^ 2, 1), (s₈ ^ 2, 1),
    (s₃ ^ 4, 1), (s₅ ^ 4, 1), (s₇ ^ 4, 1),
    (pcomm s₁ s₂, 1), (pcomm s₁ s₃, 1), (pcomm s₁ s₅, 1),
    (pcomm s₁ s₆, r₃), (pcomm s₁ s₇, s₂ * r₃ * r₅), (pcomm s₁ s₈, s₇ ^ 2 * r₃ * s₁),
    (pcomm s₂ s₄, 1), (pcomm s₂ s₆, 1), (pcomm s₂ s₈, s₄ * s₆), (pcomm s₇ s₂, s₄ * r₅),
    (pcomm s₇ s₄, r₃ * r₅), (pcomm s₃ s₅, s₂ * r₃ * s₄), (pcomm s₅ s₄, r₃),
    ((r₁ * r₈) ^ 8, 1), ((s₁ * r₁) ^ 5, 1), ((r₈ * s₈) ^ 3, 1),
    (r₁ * s₂ * r₁, s₈), (r₁ * s₄ * r₁, s₆), (r₁ * s₅ * r₁, (s₁ * r₁) ^ 2 * s₅),
    (r₁ * s₃ * r₁, (s₁ * r₁) ^ 2 * r₇), (r₁ * r₃ * r₁, s₇ * r₇),
    (r₈ * s₂ * r₈, s₆), (r₈ * s₄ * r₈, s₄), (r₈ * s₁ * r₈, s₇ * r₇), (r₈ * s₇ * r₈, s₇⁻¹),
    (r₈ * s₃ * r₈, s₇ * s₅), (r₈ * r₃ * r₈, r₅)]

@[expose] def parrottRelators : Set (FreeGroup (Fin 10)) :=
  {r | ∃ p ∈ parrottRelations, r = p.1 * p.2⁻¹}

abbrev ParrottGroup : Type := PresentedGroup parrottRelators

@[expose] def parrottWords : List (List (Fin 10 × Bool)) :=
  parrottRelations.map fun p => (p.1 * p.2⁻¹).toWord

theorem parrottRelators_eq :
    parrottRelators = {r : FreeGroup (Fin 10) | r ∈ parrottWords.map FreeGroup.mk} := by
  ext r
  simp only [parrottRelators, parrottWords, Set.mem_ofPred_eq, List.map_map, List.mem_map,
    Function.comp_def, FreeGroup.mk_toWord]
  exact ⟨fun ⟨p, hp, e⟩ => ⟨p, hp, e.symm⟩, fun ⟨p, hp, e⟩ => ⟨p, hp, e.symm⟩⟩

@[expose] noncomputable def parrottEquivPG : ParrottGroup ≃* PG 10 parrottWords :=
  QuotientGroup.quotientMulEquivOfEq (by rw [parrottRelators_eq])

theorem lift_relators_iff {X : Type*} [Group X] (ρ : Fin 10 → X) :
    (∀ p ∈ parrottRelations, FreeGroup.lift ρ p.1 = FreeGroup.lift ρ p.2) ↔
      ∀ r ∈ parrottRelators, FreeGroup.lift ρ r = 1 := by
  constructor
  · rintro h _ ⟨p, hp, rfl⟩
    rw [map_mul, map_inv, h p hp, mul_inv_cancel]
  · intro h p hp
    have := h _ ⟨p, hp, rfl⟩
    rwa [map_mul, map_inv, mul_inv_eq_one] at this

end CFSG.Literature.ParrottTits
