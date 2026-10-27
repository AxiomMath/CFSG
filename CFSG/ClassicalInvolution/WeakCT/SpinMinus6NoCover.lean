module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6PPart
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Cover

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Universal.Spin

universe u

theorem spinMinus6_noCover_odd {F : Type} [Field F] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (h5 : 5 ≤ Nat.card F) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoCover.{u} Odd (spinGroup (quadMinus 3 F b c)) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hF
      omega
    · exact h
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp2).pow
  refine NoCover.odd_of_pPrime (p := p) ?_ (spinMinus6_noCover_pPrime hp2 hF h5 hirr)
  intro E _ _ _ π hπ hcen ⟨k, hk⟩
  exact spinMinus6_ker_eq_bot_of_isPGroup hirr hF hf h2 hodd h5 hπ hcen (IsPGroup.of_card hk)

end CFSG.ClassicalInvolution.WeakCT
