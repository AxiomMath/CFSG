module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SylowTwoFactor

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup

variable {G : Type*} [Group G]

theorem factorization_eq_of_maximal_pGroup {p : ℕ} [hp : Fact p.Prime] [Finite G]
    {V : Subgroup G} (hV : IsPGroup p V) (hmax : ∀ Q : Subgroup G, IsPGroup p Q → V ≤ Q → Q = V)
    {k : ℕ} (hk : Nat.card V = p ^ k) : (Nat.card G).factorization p = k := by
  obtain ⟨P, hVP⟩ := hV.exists_le_sylow
  have hPV : (P : Subgroup G) = V := hmax P P.isPGroup' hVP
  have hcard := P.card_eq_multiplicity
  rw [hPV, hk] at hcard
  exact (Nat.pow_right_injective hp.out.two_le hcard).symm

theorem factorization_eq_of_two_factors {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) [Finite G]
    {X Y V : Subgroup G} (hXp : IsPGroup p X) (hYp : IsPGroup p Y) (hX1 : X ≠ ⊥) (hY1 : Y ≠ ⊥)
    (hXY : X ⊓ Y = ⊥) (hXV : X ≤ V) (hYV : Y ≤ V)
    (hfac : ∀ v ∈ V, ∃ a ∈ X, ∃ b ∈ Y, v = a * b) (hVab : ∀ v ∈ V, ∀ w ∈ V, Commute v w)
    (hmax : ∀ a ∈ X, a ≠ 1 → ∀ b ∈ Y, b ≠ 1 → ∀ Q : Subgroup G, IsPGroup p Q → V ≤ Q →
      Q ≤ centralizer ({a * b} : Set G) → Q = V)
    (hconj : ∀ g : G, ∀ c : G, (c ∈ X ∨ c ∈ Y) → c ≠ 1 → ∀ a ∈ X, a ≠ 1 → ∀ b ∈ Y, b ≠ 1 →
      g * c * g⁻¹ ≠ a * b)
    (hVp : IsPGroup p V) {k : ℕ} (hk : Nat.card V = p ^ k) :
    (Nat.card G).factorization p = k :=
  factorization_eq_of_maximal_pGroup hVp
    (fun _ hQ hVQ => eq_of_isPGroup_of_two_factors hp hXp hYp hX1 hY1 hXY hXV hYV hfac hVab hmax
      hconj hQ hVQ) hk

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
