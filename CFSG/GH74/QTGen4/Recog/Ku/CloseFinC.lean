module

public import CFSG.Quasithin.Recognition.HSTypeS6

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

def cfThreeCycles : List (Equiv.Perm (Fin 6)) :=
  [Equiv.swap (2 : Fin 6) 3 * Equiv.swap (3 : Fin 6) 4, Equiv.swap (2 : Fin 6) 4 * Equiv.swap (4 : Fin 6) 3,
   Equiv.swap (2 : Fin 6) 3 * Equiv.swap (3 : Fin 6) 5, Equiv.swap (2 : Fin 6) 5 * Equiv.swap (5 : Fin 6) 3,
   Equiv.swap (2 : Fin 6) 4 * Equiv.swap (4 : Fin 6) 5, Equiv.swap (2 : Fin 6) 5 * Equiv.swap (5 : Fin 6) 4,
   Equiv.swap (3 : Fin 6) 4 * Equiv.swap (4 : Fin 6) 5, Equiv.swap (3 : Fin 6) 5 * Equiv.swap (5 : Fin 6) 4]

theorem card_centralizer_stab_order_three : ∀ τ : Equiv.Perm (Fin 6),
    Equiv.Perm.sign τ = 1 → τ ^ 3 = 1 → τ ≠ 1 → actS6 τ (spE 0) = spE 0 →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 6) =>
      Equiv.Perm.sign σ = 1 ∧ actS6 σ (spE 0) = spE 0 ∧ σ * τ = τ * σ).card = 3 := by
  decide +kernel

theorem no_invert_fixing : ∀ τ : Equiv.Perm (Fin 6), Equiv.Perm.sign τ = 1 → τ ^ 3 = 1 →
    τ ≠ 1 → actS6 τ (spE 0) = spE 0 → ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
      σ * τ * σ⁻¹ = τ⁻¹ → ∃ v : SpV, actS6 τ v = v ∧ actS6 σ v ≠ v := by
  have hmem : ∀ τ : Equiv.Perm (Fin 6), τ ^ 3 = 1 → τ ≠ 1 → actS6 τ (spE 0) = spE 0 →
      ∃ c ∈ cfThreeCycles, τ = c := by
    decide +kernel
  have key : ∀ c ∈ cfThreeCycles, ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
      σ * c * σ⁻¹ = c⁻¹ → ∃ v : SpV, actS6 c v = v ∧ actS6 σ v ≠ v := by
    decide +kernel
  intro τ _ h3 h1 hfix σ hσ hinv
  obtain ⟨c, hc, hτc⟩ := hmem τ h3 h1 hfix
  rw [hτc] at hinv ⊢
  exact key c hc σ hσ hinv

end CFSG.GH74.QTGen4.Ku
