module

public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairG2

public section

namespace CFSG.ClassicalInvolution.RouteD.G2D4

open CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

theorem g2d4SharedInvolution (p : ℕ) [Fact p.Prime] : G2D4SharedInvolution p := by
  intro t n e hadm hp2 ht P hperf c₁ c₂ hc₁sq hc₁ hc₂ hc₂P hc₂cent hc₁cent
  have he : 1 ≤ e := hadm.2.1
  rcases ht with rfl | rfl
  · have hK : Odd (Nat.card (GaloisField p e)) := by
      rw [GaloisField.card p e (by omega)]
      exact odd_pow_of_ne_two p hp2 e
    rcases CFSG.ClassicalInvolution.Balance.Bootstrap.g2_eq_one_or_eq_of_central_in_perfect
      (K := GaloisField p e) hK (t := c₁) hc₁sq hc₁ hc₁cent hperf hc₂P hc₂cent with h | h
    · exact absurd h hc₂
    · exact h
  · exact ModelFacts.trialityD4_eq_of_central_in_perfect p e hp2 he hperf hc₁sq hc₁ hc₂ hc₂P
      hc₂cent hc₁cent

end CFSG.ClassicalInvolution.RouteD.G2D4
