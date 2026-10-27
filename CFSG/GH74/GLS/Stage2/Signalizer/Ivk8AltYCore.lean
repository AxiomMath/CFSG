module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltYCount

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltY

open Equiv Equiv.Perm Subgroup

theorem moved_card_dichotomy {n e : ℕ} {P W : Subgroup (Perm (Fin n))}
    (hPA : P ≤ alternatingGroup (Fin n)) (hPc : Nat.card P = 2 ^ e)
    (hbad : ∀ k < n, 1 ≤ k → k % 3 = 0 → ¬ (2 * 2 ^ e ∣ k.factorial * (n - k).factorial))
    (hW : IsPGroup 3 ↥W) (hN : P ≤ normalizer (W : Set (Perm (Fin n)))) :
    movedSet W = ∅ ∨ (movedSet W).card = n := by
  have hmod := card_movedSet_mod hW
  have hle : (movedSet W).card ≤ n := by simpa using Finset.card_le_univ (movedSet W)
  by_cases hk0 : (movedSet W).card = 0
  · exact Or.inl (Finset.card_eq_zero.1 hk0)
  right
  by_contra hlt
  have hlt' : (movedSet W).card < n := lt_of_le_of_ne hle hlt
  have hd := two_mul_card_dvd (movedSet W) (Or.inl (by omega)) P hPA (movedSet_invariant hN)
  rw [hPc] at hd
  exact hbad _ hlt' (by omega) hmod hd

theorem three_group_trivial {n e : ℕ} (hne : (n = 5 ∧ e = 2) ∨ (n = 8 ∧ e = 6) ∨ (n = 10 ∧ e = 7))
    {P W : Subgroup (Perm (Fin n))} (hPA : P ≤ alternatingGroup (Fin n))
    (hPc : Nat.card P = 2 ^ e) (hW : IsPGroup 3 ↥W)
    (hN : P ≤ normalizer (W : Set (Perm (Fin n)))) : W = ⊥ := by
  have hbad : ∀ k < n, 1 ≤ k → k % 3 = 0 → ¬ (2 * 2 ^ e ∣ k.factorial * (n - k).factorial) := by
    rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  rcases moved_card_dichotomy hPA hPc hbad hW hN with h | h
  · exact movedSet_eq_empty_iff.1 h
  · exfalso
    have := card_movedSet_mod hW
    rw [h] at this
    rcases hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltY
