module

public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LieType.SeitzGeneration.OuterSpPair

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.RankThree.PartOne.CTP

theorem subfieldPairSpOdd_of_ne_two (K : Type) [Field K] [Finite K]
    (k : Subfield K) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p)
    (hk : Nat.card k ≠ 2) (r : ℕ) (hr : 2 ≤ r) (A : gsp r K)
    (hne : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k) :
    Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
      ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) = ⊤ := by
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  exact subfieldPairSp_of_three_le k p hp hp2 hK (by omega) hr A hne

@[expose] def SubfieldPairSpF2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (k : Subfield K) (p : ℕ), p.Prime → p ≠ 2 →
    Nat.card K = Nat.card k ^ p → Nat.card k = 2 → ∀ r : ℕ, 2 ≤ r → ∀ A : gsp r K,
      (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k →
      Subgroup.closure ((spSub r k : Set (StatedSp r K)) ∪
        ((spSub r k).map (conjSp r K A).toMonoidHom : Set (StatedSp r K))) = ⊤

theorem subfieldPairSpOdd (hF2 : SubfieldPairSpF2) :
    SubfieldPairSpOdd := by
  intro K _ _ k p hp hp2 hK r hr A hne
  by_cases hk : Nat.card k = 2
  · exact hF2 K k p hp hp2 hK hk r hr A hne
  · exact subfieldPairSpOdd_of_ne_two K k p hp hp2 hK hk r hr A hne

end CFSG.LieType.SeitzGeneration
