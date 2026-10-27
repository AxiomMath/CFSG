module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Nat.Even

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_even_class_count (c : Fin 8 → Prop) [DecidablePred c] :
    64 ≤ (Finset.univ.filter fun J : Finset (Fin 8) =>
      Even (J.filter c).card ∧ Even (J.filter fun j => ¬ c j).card).card := by
  have hbool : ∀ b : Fin 8 → Bool, 64 ≤ (Finset.univ.filter fun J : Finset (Fin 8) =>
      Even (J.filter fun j => b j = true).card ∧
      Even (J.filter fun j => b j = false).card).card := by
    decide +kernel
  let b : Fin 8 → Bool := fun j => decide (c j)
  have hfilter : (Finset.univ.filter fun J : Finset (Fin 8) =>
      Even (J.filter c).card ∧ Even (J.filter fun j => ¬ c j).card) =
      (Finset.univ.filter fun J : Finset (Fin 8) =>
      Even (J.filter fun j => b j = true).card ∧
      Even (J.filter fun j => b j = false).card) := by
    apply Finset.filter_congr
    intro J _
    have e1 : J.filter c = J.filter fun j => b j = true := by
      apply Finset.filter_congr
      intro x _
      simp [b]
    have e2 : J.filter (fun j => ¬ c j) = J.filter fun j => b j = false := by
      apply Finset.filter_congr
      intro x _
      simp [b]
    rw [e1, e2]
  rw [hfilter]
  exact hbool b

end CFSG.OddStandard.HigherRank.YamadaG23
