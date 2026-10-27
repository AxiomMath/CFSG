module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem perm_two_le_moved {π : Equiv.Perm (Fin 4)} (h : π ≠ 1) :
    2 ≤ (Finset.univ.filter fun i : Fin 4 => π i ≠ i).card := by
  revert π
  decide +kernel

theorem perm_moved_four {π π' : Equiv.Perm (Fin 4)} (h1 : π * π = 1) (h2 : π' * π' = 1)
    (hc : π * π' = π' * π) (hne : π ≠ π') (hπ : π ≠ 1) (hπ' : π' ≠ 1)
    (hm : (Finset.univ.filter fun i : Fin 4 => π i ≠ i).card ≤ 3)
    (hm' : (Finset.univ.filter fun i : Fin 4 => π' i ≠ i).card ≤ 3) :
    (Finset.univ.filter fun i : Fin 4 => (π * π') i ≠ i).card = 4 := by
  revert π π'
  decide +kernel

theorem perm_eq_swap_of_moved_two {π : Equiv.Perm (Fin 4)}
    (h : (Finset.univ.filter fun i : Fin 4 => π i ≠ i).card = 2) :
    ∃ a b : Fin 4, a ≠ b ∧ π = Equiv.swap a b := by
  revert π
  decide +kernel

private instance instDecidableIsEvenVec4' (v : Fin 4 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

theorem card_even_weight_le_three :
    Nat.card {s : Fin 4 → ZMod 2 // IsEvenVec s ∧ vecWeight s ≤ 3} = 7 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_even_weight_le_three_fixed {π : Equiv.Perm (Fin 4)} (hsq : π * π = 1) (h1 : π ≠ 1)
    (hm : (Finset.univ.filter fun i : Fin 4 => π i ≠ i).card ≤ 3) :
    Nat.card {s : Fin 4 → ZMod 2 // IsEvenVec s ∧ vecWeight s ≤ 3 ∧ ∀ i, s (π i) = s i} ≤ 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  revert π
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
