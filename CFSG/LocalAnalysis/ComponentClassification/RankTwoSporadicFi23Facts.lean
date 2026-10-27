module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi23Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi23

open Subgroup CFSG.ComponentClassification.RankTwoSporadic.Cert
  CFSG.ComponentClassification.RankTwoSporadic.RootCensus

@[expose] def Fi23CensusFactsOn (P : Subgroup (Equiv.Perm (Fin 31671))) : Prop :=
  ∃ (x : ℕ → Equiv.Perm (Fin 31671)) (T : Subgroup (Equiv.Perm (Fin 31671))),
    T ≤ P ∧ Nat.card T = 2 ^ 18 ∧
    (∀ i < 3, x i ∈ P ∧ x i ^ 2 = 1 ∧ x i ≠ 1 ∧ fixP (x i) = fi23Fix[i]! ∧
      T ≤ centralizer {x i}) ∧
    ∀ i < 3, ∀ b ∈ T, b ^ 2 = 1 → b ≠ 1 → b ≠ x i →
      MonoW P true (closure {x i, b}) ∨
        ∃ j < i, fixP b = fixP (x j) ∨ fixP (x i * b) = fixP (x j)

@[expose] def Fi23CensusFacts : Prop :=
  Fi23CensusFactsOn (closure (CFSG.RankThree.Native.permsA 31671 fi23Gens))

end CFSG.ComponentClassification.RankTwoSporadic.Fi23

end
