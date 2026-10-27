module

public import CFSG.OddTranspositions.Width

public section

namespace CFSG.GroupTheory

open CFSG.OddTranspositions

theorem swaps_no_three_commute :
    ∀ a b c d e f : Fin 5, a ≠ b → c ≠ d → e ≠ f →
      ¬ (Equiv.swap a b ≠ Equiv.swap c d ∧ Equiv.swap a b ≠ Equiv.swap e f ∧
        Equiv.swap c d ≠ Equiv.swap e f ∧
        Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b ∧
        Equiv.swap a b * Equiv.swap e f = Equiv.swap e f * Equiv.swap a b ∧
        Equiv.swap c d * Equiv.swap e f = Equiv.swap e f * Equiv.swap c d) := by
  decide +kernel

theorem swaps_widthLe_two : WidthLe (transpositions : Set (Equiv.Perm (Fin 5))) 2 := by
  rw [widthLe_two_iff]
  rintro σ hσ τ hτ ρ hρ hστ hσρ hτρ ⟨hcστ, hcσρ, hcτρ⟩
  simp only [transpositions] at hσ hτ hρ
  obtain ⟨a, b, hab, hσeq⟩ := hσ
  obtain ⟨c, d, hcd, hτeq⟩ := hτ
  obtain ⟨e, f, hef, hρeq⟩ := hρ
  subst σ
  subst τ
  subst ρ
  exact swaps_no_three_commute a b c d e f hab hcd hef
    ⟨hστ, hσρ, hτρ, hcστ, hcσρ, hcτρ⟩

end CFSG.GroupTheory
