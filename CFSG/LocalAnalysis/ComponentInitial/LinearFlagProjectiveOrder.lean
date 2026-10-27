module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_projectiveSL_dvd_card_specialLinearGroup {n : ℕ} {F : Type}
    [Field F] [Finite F] :
    Nat.card (projectiveSL n F) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) F) :=
  Subgroup.card_quotient_dvd_card (scalars n F)

theorem card_projectiveSL_dvd_card_GL {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F] :
    Nat.card (projectiveSL n F) ∣ Nat.card (GL (Fin n) F) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin n) F) ∣ Nat.card (GL (Fin n) F) :=
    ⟨Nat.card Fˣ, Matrix.card_SL_mul_card_units.symm⟩
  exact (card_projectiveSL_dvd_card_specialLinearGroup (n := n)).trans h2

end CFSG.LocalAnalysis.ComponentInitial.LinearFlag

end
