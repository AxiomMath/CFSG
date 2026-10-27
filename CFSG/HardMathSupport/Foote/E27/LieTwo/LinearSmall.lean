module

public import CFSG.HardMathSupport.Foote.E27.Split
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Assembly.LowTwoRank Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.dvd27_card_of_mem (h : E27Config X K R T z) (hz : z ∈ K) :
    27 ∣ Nat.card K := by
  have hRK : R ≤ K := h.le_of_mem hz
  have := Subgroup.card_dvd_of_le hRK
  rwa [h.card_R] at this

theorem E27Config.false_of_psl_two_small (h : E27Config X K R T z) (hz : z ∈ K) {n p f : ℕ}
    (hcl : StatedClassicalModel K .PSL n p f) (hq : p ^ f = 2) (hn : n = 3 ∨ n = 4) : False := by
  have hp : p.Prime := hcl.1.1
  have hf : 1 ≤ f := hcl.1.2.1
  have hp2 : p = 2 := by
    have : p ∣ 2 := hq ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  subst hp2
  have hf1 : f = 1 := Nat.pow_right_injective le_rfl (by simpa using hq)
  subst hf1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).1 rfl
  have h27 := h.dvd27_card_of_mem hz
  rw [hcard] at h27
  rcases hn with rfl | rfl <;> revert h27 <;> decide

end CFSG.HardMathSupport.Foote.E27
