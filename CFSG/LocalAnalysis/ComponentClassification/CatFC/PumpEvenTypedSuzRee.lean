module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTyped
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem evenOuterTypedFamilyInput_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n f : ℕ), StatedLieAdmissible τ n 2 f → LieModel K τ n 2 f →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) :
    EvenOuterTypedFamilyInput τ := by
  intro K _ n f hadm hm α hα2 hαo
  exact absurd (hτ K n f hadm hm α (hα2 ▸ pow_orderOf_eq_one α)) hαo

theorem evenOuterTypedFamilyInput_twistedB2
    : EvenOuterTypedFamilyInput .twistedB2 := by
  refine evenOuterTypedFamilyInput_of_involutions_inner fun K _ n f _ hm => ?_
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f (Or.inl ?_)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem evenOuterTypedFamilyInput_twistedF4
    : EvenOuterTypedFamilyInput .twistedF4 := by
  refine evenOuterTypedFamilyInput_of_involutions_inner fun K _ n f _ hm => ?_
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f
    (Or.inr (Or.inl ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem evenOuterTypedFamilyInput_Tits
    : EvenOuterTypedFamilyInput .Tits := by
  refine evenOuterTypedFamilyInput_of_involutions_inner fun K _ n f hadm hm => ?_
  obtain rfl : f = 1 := hadm.2.2.2.2
  refine CFSG.Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

end CFSG.ComponentClassification.CatFC
