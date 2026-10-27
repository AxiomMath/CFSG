module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang

theorem exists_card_eq_prime_pow (K : Type) [Field K] [Finite K] :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Nat.card K = p ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hn⟩ := FiniteField.card' K
  exact ⟨p, n, hp, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem finite_ringEquiv (K : Type) [Field K] [Finite K] : Finite (K ≃+* K) :=
  Finite.of_injective (fun τ : K ≃+* K => (τ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang
