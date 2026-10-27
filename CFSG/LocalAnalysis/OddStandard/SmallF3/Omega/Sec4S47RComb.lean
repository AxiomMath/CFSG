module

public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def sec4S47RTau : Equiv.Perm (Option (Fin 7)) := Equiv.swap (some 0) (some 1)

@[expose] def sec4S47RInd : Option (Fin 7) → ZMod 2 :=
  fun r => if r = some 0 ∨ r = some 1 then 1 else 0

@[expose] def sec4S47RCyc (a b c : Option (Fin 7)) : Equiv.Perm (Option (Fin 7)) :=
  Equiv.swap a b * Equiv.swap b c

theorem sec4S47R_swap_add (w : Option (Fin 7) → ZMod 2) (r : Option (Fin 7)) :
    w (sec4S47RTau r) + w r = (w (some 0) + w (some 1)) * sec4S47RInd r := by
  unfold sec4S47RTau sec4S47RInd
  by_cases h0 : r = some 0
  · subst h0
    simp [Equiv.swap_apply_left, add_comm]
  · by_cases h1 : r = some 1
    · subst h1
      simp [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
      simp [h0, h1, CharTwo.add_self_eq_zero]

private theorem sec4S47R_comb_aux : ∀ v : Option (Fin 7) → ZMod 2,
    (∃ ε : ZMod 2, ∀ r, v (sec4S47RTau.symm r) + v r = ε) →
    (∃ e ε : ZMod 2, ∀ r,
      v ((sec4S47RCyc none (some 2) (some 3)).symm r) + v r = e * sec4S47RInd r + ε) →
    (∃ e ε : ZMod 2, ∀ r,
      v ((sec4S47RCyc (some 3) (some 4) (some 5)).symm r) + v r = e * sec4S47RInd r + ε) →
    (∃ e ε : ZMod 2, ∀ r,
      v ((sec4S47RCyc (some 5) (some 6) none).symm r) + v r = e * sec4S47RInd r + ε) →
    ∃ e ε : ZMod 2, ∀ r, v r = e * sec4S47RInd r + ε := by
  unfold sec4S47RTau sec4S47RCyc sec4S47RInd
  decide +kernel

theorem sec4S47R_comb (v : Option (Fin 7) → ZMod 2)
    (hτ : ∃ ε : ZMod 2, ∀ r, v (sec4S47RTau.symm r) + v r = ε)
    (h₁ : ∃ e ε : ZMod 2, ∀ r,
      v ((sec4S47RCyc none (some 2) (some 3)).symm r) + v r = e * sec4S47RInd r + ε)
    (h₂ : ∃ e ε : ZMod 2, ∀ r,
      v ((sec4S47RCyc (some 3) (some 4) (some 5)).symm r) + v r = e * sec4S47RInd r + ε)
    (h₃ : ∃ e ε : ZMod 2, ∀ r,
      v ((sec4S47RCyc (some 5) (some 6) none).symm r) + v r = e * sec4S47RInd r + ε) :
    ∃ e ε : ZMod 2, ∀ r, v r = e * sec4S47RInd r + ε :=
  sec4S47R_comb_aux v hτ h₁ h₂ h₃

end CFSG.OddStandard.SmallF3.Omega
