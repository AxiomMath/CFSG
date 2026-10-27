module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenBasic
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem a2l_evenTCOuter_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f →
      Blueprint.LieModel K τ n 2 f →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) :
    EvenTCOuter τ := by
  intro K _ n f hadm hm α hα2 hαo
  exact absurd (hτ K n f hadm hm α (hα2 ▸ pow_orderOf_eq_one α)) hαo

theorem a2l_evenTCOuter_twistedB2
    (_hO : LieOrderFormulasInput) : EvenTCOuter .twistedB2 := by
  refine a2l_evenTCOuter_of_involutions_inner fun K _ n f _ hm => ?_
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f (Or.inl ?_)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem a2l_evenTCOuter_twistedF4
    (_hO : LieOrderFormulasInput) : EvenTCOuter .twistedF4 := by
  refine a2l_evenTCOuter_of_involutions_inner fun K _ n f _ hm => ?_
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f
    (Or.inr (Or.inl ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem a2l_evenTCOuter_Tits
    (_hO : LieOrderFormulasInput) : EvenTCOuter .Tits := by
  refine a2l_evenTCOuter_of_involutions_inner fun K _ n f hadm hm => ?_
  obtain rfl : f = 1 := hadm.2.2.2.2
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

end CFSG.OddStandard.SmallF3.HypA2Leaves
