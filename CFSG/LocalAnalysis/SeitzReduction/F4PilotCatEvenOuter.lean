module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatStatement
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def CatSp6EvenOuterFamily (τ : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n e : ℕ, StatedLieAdmissible τ n 2 e → LieModel S τ n 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp 3 2 f →
      FixedCentralizerTwoFree σ D →
        Sp6OvergroupType S f ∧ LieModel (fixedSubgroup σ) .PSp 3 2 f

theorem catSp6EvenOuter_of_families (h : ∀ τ, CatSp6EvenOuterFamily τ) : CatSp6EvenOuter := by
  intro S _ _ hS hna heven σ hσ hout f D hD hD6 hodd
  obtain ⟨τ, n, e, hadm, hm⟩ := heven
  exact h τ S hS hna n e hadm hm σ hσ hout f D hD hD6 hodd

theorem catSp6EvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n e : ℕ, ¬ StatedLieAdmissible τ n 2 e) : CatSp6EvenOuterFamily τ :=
  fun _ _ _ _ _ n e hadm => absurd hadm (hτ n e)

theorem catSp6EvenOuterFamily_POmegaOdd : CatSp6EvenOuterFamily .POmegaOdd :=
  catSp6EvenOuterFamily_of_not_admissible fun _ _ hadm => hadm.2.2.2 rfl

theorem catSp6EvenOuterFamily_twistedG2 : CatSp6EvenOuterFamily .twistedG2 :=
  catSp6EvenOuterFamily_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

theorem catSp6EvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n e : ℕ), StatedLieAdmissible τ n 2 e → LieModel K τ n 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) :
    CatSp6EvenOuterFamily τ := by
  intro S _ _ _ _ n e hadm hm σ hσ hout
  exact absurd (hτ S n e hadm hm σ (hσ ▸ pow_orderOf_eq_one σ)) hout

section SuzukiReeTits


theorem catSp6EvenOuterFamily_twistedB2 : CatSp6EvenOuterFamily .twistedB2 := by
  refine catSp6EvenOuterFamily_of_involutions_inner fun K _ n e _ hm => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem catSp6EvenOuterFamily_twistedF4 : CatSp6EvenOuterFamily .twistedF4 := by
  refine catSp6EvenOuterFamily_of_involutions_inner fun K _ n e _ hm => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSp6EvenOuterFamily_Tits : CatSp6EvenOuterFamily .Tits := by
  refine catSp6EvenOuterFamily_of_involutions_inner fun K _ n e hadm hm => ?_
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSp6EvenOuter_of_open_families (hPSL : CatSp6EvenOuterFamily .PSL)
    (hPSU : CatSp6EvenOuterFamily .PSU) (hPSp : CatSp6EvenOuterFamily .PSp)
    (hOp : CatSp6EvenOuterFamily .POmegaPlus) (hOm : CatSp6EvenOuterFamily .POmegaMinus)
    (hG2 : CatSp6EvenOuterFamily .G2) (hF4 : CatSp6EvenOuterFamily .F4)
    (hE6 : CatSp6EvenOuterFamily .E6) (hE7 : CatSp6EvenOuterFamily .E7)
    (hE8 : CatSp6EvenOuterFamily .E8) (h2E6 : CatSp6EvenOuterFamily .twistedE6)
    (h3D4 : CatSp6EvenOuterFamily .trialityD4) : CatSp6EvenOuter := by
  apply catSp6EvenOuter_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact catSp6EvenOuterFamily_POmegaOdd
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact catSp6EvenOuterFamily_twistedB2
  · exact catSp6EvenOuterFamily_twistedG2
  · exact catSp6EvenOuterFamily_twistedF4
  · exact catSp6EvenOuterFamily_Tits

end SuzukiReeTits

end CFSG.SeitzReduction.F4Pilot
