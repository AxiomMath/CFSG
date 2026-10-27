module

public import CFSG.LieType.SeitzGeneration.UnitarySplit
public import CFSG.LieType.SeitzGeneration.Classical

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def UnitarySUNonsplit : Prop :=
  ∀ (ℓ f p n : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → p.Prime → 5 ≤ p → p ≠ ℓ →
    ¬ p ∣ ℓ ^ f + 1 → ¬ p ∣ ℓ ^ f - 1 → 3 ≤ n → ∀ E : Subgroup (unitarySU ℓ f K n),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤

theorem unitarySUNontoral_of_nonsplit (h : UnitarySUNonsplit) : UnitarySUNontoral := by
  intro ℓ f p n K _ hU hp hp5 hpℓ hpq1 hn E hcomm hexp hcard
  by_cases hpq : p ∣ ℓ ^ f - 1
  · exact unitarySU_planeGen_split hU hp (by omega) hpq (by omega) E hcomm hexp hcard
  · exact h ℓ f p n K hU hp hp5 hpℓ hpq1 hpq hn E hcomm hexp hcard

theorem kFactSeitzRankTwo_of_nonsplit_leaves (hU : UnitarySUNonsplit) (hO : OrthogonalOddPlanes)
    (hP : OrthogonalPlusPlanes) (hM : OrthogonalMinusPlanes) (hN : SeitzInnerClassicalNonab)
    (hX : SeitzInnerExceptionalFive) (h3 : SeitzInnerThree) (ho : KFactSeitzRankTwoOuter) :
    KFactSeitzRankTwo :=
  kFactSeitzRankTwo_of_leaves (unitarySUNontoral_of_nonsplit hU) hO hP hM hN hX h3 ho

end CFSG.LieType.SeitzGeneration
