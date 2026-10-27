module

public import CFSG.Quasithin.Recognition.HSTypeS6

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

theorem fix_eq_commutator_of_invol : ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 →
    σ * σ = 1 → σ ≠ 1 → ∀ v : SpV, actS6 σ v = v → ∃ u : SpV, v = u + actS6 σ u := by
  decide +kernel

theorem card_fix_order_three : ∀ τ : Equiv.Perm (Fin 6), Equiv.Perm.sign τ = 1 → τ ^ 3 = 1 →
    τ ≠ 1 → actS6 τ (spE 0) = spE 0 →
    (Finset.univ.filter fun v : SpV => actS6 τ v = v).card = 4 := by
  decide +kernel

end CFSG.GH74.QTGen4.Ku
