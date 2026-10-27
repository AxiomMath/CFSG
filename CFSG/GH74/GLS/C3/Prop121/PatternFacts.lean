module

public import CFSG.GH74.GLS.C3.Prop121.Interfaces
public import CFSG.GH74.GLS.C3.Layer3.PatternClasses
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.Layer3

namespace PatternAux

theorem altX_altY_classes {N : ℕ} (h8 : 8 ≤ N) (h11 : N ≤ 11) :
    ¬ IsConj (altX h8) (altY h8) ∧
      ∀ w : alternatingGroup (Fin N), orderOf w = 2 → IsConj (altX h8) w ∨ IsConj (altY h8) w := by
  refine ⟨?_, ?_⟩
  · intro h
    have h' : IsConj (xPerm h8) (yPerm h8) :=
      (isConj_iff.2 (by obtain ⟨c, hc⟩ := isConj_iff.1 h; exact ⟨(c : Perm (Fin N)),
        congrArg Subtype.val hc⟩))
    rw [isConj_iff_cycleType_eq, xPerm_cycleType, yPerm_cycleType] at h'
    exact absurd h' (by decide)
  · intro w hw
    have hσ : orderOf (w : Perm (Fin N)) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
    have hs : sign (w : Perm (Fin N)) = 1 := mem_alternatingGroup.1 w.2
    rcases involution_cycleType_cases h11 _ hσ hs with h | h
    · left
      refine isConj_alt_of_perm _ _ ?_ _ (sign_swap01 h8) (swap01_comm_xPerm h8)
      exact isConj_iff_cycleType_eq.2 (by rw [h]; exact xPerm_cycleType h8)
    · right
      refine isConj_alt_of_perm _ _ ?_ _ (sign_swap01 h8) (swap01_comm_yPerm h8)
      exact isConj_iff_cycleType_eq.2 (by rw [h]; exact yPerm_cycleType h8)

theorem four_factorial_ne {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) :
    4 * n.factorial ≠ 192 * (n - 4).factorial := by
  rcases hn with rfl | rfl | rfl <;> decide

end PatternAux

theorem patternFacts_of_approx {G : Type} [Group G] [Finite G] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7) (hA : IsApproxTo G (alternatingGroup (Fin (n + 4)))) :
    PatternFacts G n := by
  have h8 : 8 ≤ n + 4 := by omega
  have h11 : n + 4 ≤ 11 := by omega
  obtain ⟨hab, hcl⟩ := PatternAux.altX_altY_classes h8 h11
  obtain ⟨x, y, hx, hy, -, hclG, hcx, hcy⟩ :=
    pattern_two_classes_card hA.1 (orderOf_altX h8) (orderOf_altY h8) hab hcl
  have hX : Nat.card (centralizer ({altX h8} : Set (alternatingGroup (Fin (n + 4))))) =
      4 * n.factorial := by
    have h := card_centralizer_altX h8
    rw [Nat.add_sub_cancel] at h
    omega
  have hY : Nat.card (centralizer ({altY h8} : Set (alternatingGroup (Fin (n + 4))))) =
      192 * (n - 4).factorial := by
    have h := card_centralizer_altY h8
    have e : n + 4 - 8 = n - 4 := by omega
    rw [e] at h
    omega
  have hne : 4 * n.factorial ≠ 192 * (n - 4).factorial := PatternAux.four_factorial_ne hn
  have key : ∀ w : G, orderOf w = 2 → Nat.card (centralizer ({w} : Set G)) = 4 * n.factorial →
      IsConj x w := by
    intro w hw hcw
    rcases hclG w hw with h | h
    · exact h
    · exfalso
      apply hne
      rw [← hcw, ← Layer3.card_centralizer_eq_of_isConj h, hcy, hY]
  refine ⟨fun w hw => ?_, fun w w' hw hw' hcw hcw' => ?_⟩
  · rcases hclG w hw with h | h
    · left
      rw [← Layer3.card_centralizer_eq_of_isConj h, hcx, hX]
    · right
      rw [← Layer3.card_centralizer_eq_of_isConj h, hcy, hY]
  · exact (key w hw hcw).symm.trans (key w' hw' hcw')

end CFSG.GH74.GLS.C3.Prop121
