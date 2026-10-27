module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {X : Type*} [Group X]

@[expose] noncomputable def planeAct {K D : Subgroup X} (hDN : D ≤ Subgroup.normalizer (K : Set X)) :
    D →* MulAut K :=
  (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hDN)

theorem planeAct_range_card_eq_pow {p : ℕ} (hp : p.Prime) {K D : Subgroup X}
    (hDN : D ≤ Subgroup.normalizer (K : Set X)) (hcard : Nat.card D = p ^ 2) :
    ∃ j ≤ 2, Nat.card (planeAct hDN).range = p ^ j := by
  have hsum := Subgroup.card_ker_mul_card_range (planeAct hDN)
  rw [hcard] at hsum
  have hdvd : Nat.card (planeAct hDN).range ∣ p ^ 2 := Dvd.intro_left _ hsum
  exact (Nat.dvd_prime_pow hp).1 hdvd

end CFSG.HardMathSupport.Timmesfeld.Proving
