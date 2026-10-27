module

public import CFSG.Quasithin.Recognition.HSTypeS6

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

theorem exists_alt_act_spE0 : ∀ v : SpV, v ≠ 0 →
    ∃ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ actS6 σ (spE 0) = v := by
  decide +kernel

theorem alt_six_invol_conj : ∀ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 → σ * σ = 1 →
    σ ≠ 1 → ∃ ρ : Equiv.Perm (Fin 6), Equiv.Perm.sign ρ = 1 ∧
      ρ * σ * ρ⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  decide +kernel

end CFSG.GH74.QTGen4.Ku
