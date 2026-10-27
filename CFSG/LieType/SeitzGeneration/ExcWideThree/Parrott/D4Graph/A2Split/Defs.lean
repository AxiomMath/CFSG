module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP


@[expose] def D4GraphA2PairGenSplit : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 → 4 ≤ Nat.card K →
    ∀ B : SL2 K, B ^ 3 = 1 → B ≠ 1 → PairGenAt (gammaP K B)

@[expose] def D4GraphA2PairGenNonsplit : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → 4 ≤ Nat.card K →
    ∀ B : SL2 K, B ^ 3 = 1 → B ≠ 1 → PairGenAt (gammaP K B)

theorem card_mod_three_ne_zero {K : Type} [Field K] [Finite K] (h3 : ringChar K ≠ 3) :
    Nat.card K % 3 ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn]
  intro h0
  have h3d : 3 ∣ ringChar K ^ (n : ℕ) := Nat.dvd_of_mod_eq_zero h0
  have h3p : 3 ∣ ringChar K := Nat.prime_three.dvd_of_dvd_pow h3d
  rcases (Nat.dvd_prime hp).1 h3p with h | h
  · exact absurd h (by norm_num)
  · exact h3 h.symm

theorem d4GraphA2PairGen_of_split (h1 : D4GraphA2PairGenSplit) (h2 : D4GraphA2PairGenNonsplit) :
    D4GraphA2PairGen := by
  intro K _ _ hK3 hK4 B hB3 hB1
  have h0 := card_mod_three_ne_zero hK3
  have hlt : Nat.card K % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2) with h | h
  · exact h1 K h hK4 B hB3 hB1
  · exact h2 K h hK4 B hB3 hB1

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
