module

public import CFSG.GH74.KGroups.Checks

public section

namespace CFSG.GH74.KGroups

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def noOrdersCheck (L : List (Equiv.Perm (Fin n))) (m₁ m₂ : ℕ) : Bool :=
  L.all fun g => !orderIs g m₁ && !orderIs g m₂

theorem noOrdersCheck_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) {m₁ m₂ : ℕ}
    (h₁ : 0 < m₁) (h₂ : 0 < m₂) (h : noOrdersCheck (elemsT Q) m₁ m₂ = true) :
    ∀ g ∈ Q.originalSubgroup, orderOf g ≠ m₁ ∧ orderOf g ≠ m₂ := by
  intro g hg
  have := List.all_eq_true.1 h g ((mem_elemsT Q hQ g).2 hg)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have := (orderIs_iff g h₁).2 e
    simp [this] at *
  · have := (orderIs_iff g h₂).2 e
    simp [this] at *

@[expose] def e8at (X : Equiv.Perm (Fin n)) (C : List (Equiv.Perm (Fin n))) : Bool :=
  C.all fun Y => C.all fun Z =>
    decide (Y * Z ≠ Z * Y) || decide (Y ∈ ([1, X] : List (Equiv.Perm (Fin n)))) ||
      decide (Z ∈ ([1, X, Y, X * Y] : List (Equiv.Perm (Fin n))))

@[expose] def e8free (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.all fun X => bif decide (X ^ 2 = 1) && decide (X ≠ 1) then
    e8at X (L.filter (fun g => decide (g ^ 2 = 1 ∧ g * X = X * g))) else true

theorem e8free_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : e8free (elemsT Q) = true) :
    ∀ X ∈ Q.originalSubgroup, ∀ Y ∈ Q.originalSubgroup, ∀ Z ∈ Q.originalSubgroup,
      X ^ 2 = 1 → Y ^ 2 = 1 → Z ^ 2 = 1 → X * Y = Y * X → X * Z = Z * X → Y * Z = Z * Y →
      X = 1 ∨ Y ∈ ([1, X] : List (Equiv.Perm (Fin n))) ∨
        Z ∈ ([1, X, Y, X * Y] : List (Equiv.Perm (Fin n))) := by
  intro X hX Y hY Z hZ hX2 hY2 hZ2 hXY hXZ hYZ
  by_cases hX1 : X = 1
  · exact Or.inl hX1
  · have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h X ((mem_elemsT Q hQ X).2 hX))
      (by simp [hX2, hX1])
    have h2 := List.all_eq_true.1 h1 Y (by
      rw [List.mem_filter]
      exact ⟨(mem_elemsT Q hQ Y).2 hY, by simpa using ⟨hY2, hXY.symm⟩⟩)
    have h3 := List.all_eq_true.1 h2 Z (by
      rw [List.mem_filter]
      exact ⟨(mem_elemsT Q hQ Z).2 hZ, by simpa using ⟨hZ2, hXZ.symm⟩⟩)
    simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq] at h3
    rcases h3 with (h3 | h3) | h3
    · exact absurd hYZ h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h3)

end CFSG.GH74.KGroups
