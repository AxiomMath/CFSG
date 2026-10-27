module

public import CFSG.LieType.SeitzGeneration.OrthRest
public import CFSG.LieType.SeitzGeneration.OrthEvenBig

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.RankThree.Classical CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def OrthSelfDualRestFour : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) → 7 ≤ finrank K V →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ ringChar K → RankLE2 p (orthDerived Q) →
    ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 → (∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) → HasSelfDualFactor Q E →
      finrank K V ≤ finrank K ↥(planeFixSpace E) + 8 →
        Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤

theorem orthSelfDualRest_of_restFour (hrest : OrthSelfDualRestFour) : OrthSelfDualRest := by
  intro K V _ _ _ _ _ Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard haniso hsd h2
  by_cases h8 : finrank K V ≤ finrank K ↥(planeFixSpace E) + 8
  · exact hrest K V Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard haniso hsd h8
  · push Not at h8
    exact OrthBlk.closure_eq_top_of_selfdual_big_even hQ hT hp hp5 hpl (h2.resolve_right
      (by omega)) hrank E hcomm hexp hcard haniso hsd h8

theorem orthSelfDualTwoBlocks_of_restFour (hrest : OrthSelfDualRestFour) :
    OrthSelfDualTwoBlocks :=
  orthSelfDualTwoBlocks_of_rest (orthSelfDualRest_of_restFour hrest)

end CFSG.LieType.SeitzGeneration
