module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenBasic
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Even

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem evenFiveOuter_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f →
      Blueprint.LieModel K τ n 2 f →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) :
    EvenFiveOuter τ := by
  intro K _ n f hadm hm α hα2 hαo
  exact absurd (hτ K n f hadm hm α (hα2 ▸ pow_orderOf_eq_one α)) hαo

theorem evenFiveOuter_twistedB2
    (_hO : LieOrderFormulasInput) : EvenFiveOuter .twistedB2 := by
  refine evenFiveOuter_of_involutions_inner fun K _ n f _ hm => ?_
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f (Or.inl ?_)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem evenFiveOuter_twistedF4
    (_hO : LieOrderFormulasInput) : EvenFiveOuter .twistedF4 := by
  refine evenFiveOuter_of_involutions_inner fun K _ n f _ hm => ?_
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f
    (Or.inr (Or.inl ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem evenFiveOuter_Tits
    (_hO : LieOrderFormulasInput) : EvenFiveOuter .Tits := by
  refine evenFiveOuter_of_involutions_inner fun K _ n f hadm hm => ?_
  obtain rfl : f = 1 := hadm.2.2.2.2
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat.Even
