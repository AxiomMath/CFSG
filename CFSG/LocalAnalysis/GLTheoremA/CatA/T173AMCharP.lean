module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p', hp'⟩ := CharP.exists F
  have hp'prime : p'.Prime := CharP.char_is_prime F p'
  obtain ⟨m, -, hcard⟩ := FiniteField.card F p'
  have hdvd : p' ∣ 2 ^ n := by
    rw [← hF, Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p' m.pos.ne'
  have h2 : p' ∣ 2 := hp'prime.dvd_of_dvd_pow hdvd
  have : p' = 2 := (Nat.prime_dvd_prime_iff_eq hp'prime Nat.prime_two).mp h2
  subst this
  exact hp'

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
