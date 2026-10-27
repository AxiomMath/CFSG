module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatStatement
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def CatE7EvenOuterFamily (τ : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n e : ℕ, StatedLieAdmissible τ n 2 e → LieModel S τ n 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .E7 0 2 f →
      LieModel S .E7 0 2 (2 * f) ∧ LieModel (fixedSubgroup σ) .E7 0 2 f

theorem catE7EvenOuter_of_families (h : ∀ τ, CatE7EvenOuterFamily τ) : CatE7EvenOuter := by
  intro S _ _ hS hna heven σ hσ hout f D hD hD7
  obtain ⟨τ, n, e, hadm, hm⟩ := heven
  exact h τ S hS hna n e hadm hm σ hσ hout f D hD hD7

theorem catE7EvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n e : ℕ, ¬ StatedLieAdmissible τ n 2 e) : CatE7EvenOuterFamily τ :=
  fun _ _ _ _ _ n e hadm => absurd hadm (hτ n e)

theorem catE7EvenOuterFamily_POmegaOdd : CatE7EvenOuterFamily .POmegaOdd :=
  catE7EvenOuterFamily_of_not_admissible fun _ _ hadm => hadm.2.2.2 rfl

theorem catE7EvenOuterFamily_twistedG2 : CatE7EvenOuterFamily .twistedG2 :=
  catE7EvenOuterFamily_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

theorem catE7EvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n e : ℕ), StatedLieAdmissible τ n 2 e → LieModel K τ n 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) :
    CatE7EvenOuterFamily τ := by
  intro S _ _ _ _ n e hadm hm σ hσ hout
  exact absurd (hτ S n e hadm hm σ (hσ ▸ pow_orderOf_eq_one σ)) hout

theorem catE7EvenOuterFamily_of_forall_false {τ : StatedLieTag}
    (hτ : ∀ (S : Type) [Group S] [Finite S] (n e : ℕ), StatedLieAdmissible τ n 2 e →
      LieModel S τ n 2 e → ∀ σ : MulAut S, orderOf σ = 2 →
      σ ∉ (MulAut.conj : S →* MulAut S).range → ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      IsComponent D → LieModel D .E7 0 2 f → False) : CatE7EvenOuterFamily τ :=
  fun S _ _ _ _ n e hadm hm σ hσ hout f D hD hD7 =>
    (hτ S n e hadm hm σ hσ hout f D hD hD7).elim

section SuzukiReeTits


theorem catE7EvenOuterFamily_twistedB2 : CatE7EvenOuterFamily .twistedB2 := by
  refine catE7EvenOuterFamily_of_involutions_inner fun K _ n e _ hm => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem catE7EvenOuterFamily_twistedF4 : CatE7EvenOuterFamily .twistedF4 := by
  refine catE7EvenOuterFamily_of_involutions_inner fun K _ n e _ hm => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catE7EvenOuterFamily_Tits : CatE7EvenOuterFamily .Tits := by
  refine catE7EvenOuterFamily_of_involutions_inner fun K _ n e hadm hm => ?_
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catE7EvenOuter_of_open_families (hPSL : CatE7EvenOuterFamily .PSL)
    (hPSU : CatE7EvenOuterFamily .PSU) (hPSp : CatE7EvenOuterFamily .PSp)
    (hOp : CatE7EvenOuterFamily .POmegaPlus) (hOm : CatE7EvenOuterFamily .POmegaMinus)
    (hG2 : CatE7EvenOuterFamily .G2) (hF4 : CatE7EvenOuterFamily .F4)
    (hE6 : CatE7EvenOuterFamily .E6) (hE7 : CatE7EvenOuterFamily .E7)
    (hE8 : CatE7EvenOuterFamily .E8) (h2E6 : CatE7EvenOuterFamily .twistedE6)
    (h3D4 : CatE7EvenOuterFamily .trialityD4) : CatE7EvenOuter := by
  apply catE7EvenOuter_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact catE7EvenOuterFamily_POmegaOdd
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact catE7EvenOuterFamily_twistedB2
  · exact catE7EvenOuterFamily_twistedG2
  · exact catE7EvenOuterFamily_twistedF4
  · exact catE7EvenOuterFamily_Tits

end SuzukiReeTits

end CFSG.SeitzReduction.E8Pilot
