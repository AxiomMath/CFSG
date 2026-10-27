module

public import CFSG.LieType.SeitzGeneration.OrthSdBig
public import CFSG.LieType.SeitzGeneration.OrthLow

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.RankThree.Classical CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def OrthSelfDualRest : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) → 7 ≤ finrank K V →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ ringChar K → RankLE2 p (orthDerived Q) →
    ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 → (∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) → HasSelfDualFactor Q E →
      ((2 : K) = 0 ∨ finrank K V ≤ finrank K ↥(planeFixSpace E) + 8) →
        Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤

theorem orthSelfDualTwoBlocks_of_rest (hrest : OrthSelfDualRest) : OrthSelfDualTwoBlocks := by
  intro K V _ _ _ _ _ Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard haniso hsd
  by_cases h2 : (2 : K) = 0 ∨ finrank K V ≤ finrank K ↥(planeFixSpace E) + 8
  · exact hrest K V Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard haniso hsd h2
  · push Not at h2
    exact OrthBlk.closure_eq_top_of_selfdual_big hQ hT hp hp5 hpl h2.1 hrank E hcomm hexp hcard
      haniso hsd h2.2

end CFSG.LieType.SeitzGeneration
