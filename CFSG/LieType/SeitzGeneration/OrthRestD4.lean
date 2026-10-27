module

public import CFSG.LieType.SeitzGeneration.OrthRestFour
public import CFSG.LieType.SeitzGeneration.OrthGenBig

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.RankThree.Classical CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def OrthSelfDualRestD4 : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ ringChar K → RankLE2 p (orthDerived Q) →
    ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 → (∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) → HasSelfDualFactor Q E →
      finrank K ↥(planeFixSpace E) = 0 → finrank K V = 8 →
        Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤

theorem orthSelfDualTwoBlocks_of_restD4 (hrest : OrthSelfDualRestD4) : OrthSelfDualTwoBlocks := by
  intro K V _ _ _ _ _ Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard haniso hsd
  rcases OrthBlk.closure_eq_top_of_selfdual_or_D4 hQ hT hdim hp hp5 hpl hrank E hcomm hexp hcard
    haniso hsd with h | ⟨h0, h8⟩
  · exact h
  · exact hrest K V Q hQ hT p hp hp5 hpl hrank E hcomm hexp hcard haniso hsd h0 h8

theorem orthSelfDualRestFour_of_restD4 (hrest : OrthSelfDualRestD4) : OrthSelfDualRestFour :=
  fun K V _ _ _ _ _ Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard haniso hsd _ =>
    orthSelfDualTwoBlocks_of_restD4 hrest K V Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard
      haniso hsd

end CFSG.LieType.SeitzGeneration
