module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem card_odd_of_two_ne_zero {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) :
    Odd (Nat.card K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hne : ringChar K ≠ 2 := by
    intro hc
    apply h2
    have hcast := CharP.cast_eq_zero K (ringChar K)
    rw [hc] at hcast
    exact_mod_cast hcast
  rw [Nat.card_eq_fintype_card, ← Nat.not_even_iff_odd]
  exact fun he => hne (FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp he))

theorem card_range_powMonoidHom_two {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (powMonoidHom 2 : Kˣ →* Kˣ).range = (Nat.card K - 1) / 2 := by
  have hodd := card_odd_of_two_ne_zero h2
  have hidx : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 2 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units]
    have he : 2 ∣ Nat.card K - 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Nat.gcd_eq_right he
  have hmul := Subgroup.card_mul_index (powMonoidHom 2 : Kˣ →* Kˣ).range
  rw [hidx, Nat.card_units] at hmul
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
