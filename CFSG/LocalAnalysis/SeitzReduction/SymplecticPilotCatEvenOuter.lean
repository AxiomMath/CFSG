module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenOuter

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

@[expose] def Sp2mOvergroupType (S : Type) [Group S] (m f : ℕ) : Prop :=
  LieModel S .PSp m 2 (2 * f) ∨ LieModel S .PSL (2 * m) 2 f ∨ LieModel S .PSU (2 * m) 2 f ∨
    LieModel S .PSL (2 * m + 1) 2 f ∨ LieModel S .PSU (2 * m + 1) 2 f ∨
    LieModel S .POmegaPlus (m + 1) 2 f ∨ LieModel S .POmegaMinus (m + 1) 2 f

theorem sp6OvergroupType_iff {S : Type} [Group S] {f : ℕ} :
    Sp2mOvergroupType S 3 f ↔ F4Pilot.Sp6OvergroupType S f :=
  Iff.rfl

@[expose] def CatSp2mEvenOuter (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp m 2 f →
      FixedCentralizerTwoFree σ D →
        Sp2mOvergroupType S m f ∧ LieModel (fixedSubgroup σ) .PSp m 2 f

@[expose] def CatSp2mEvenOuterExact (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp m 2 f →
      Sp2mOvergroupType S m f ∧ LieModel (fixedSubgroup σ) .PSp m 2 f

theorem catSp2mEvenOuter_of_exact {m : ℕ} (h : CatSp2mEvenOuterExact m) : CatSp2mEvenOuter m :=
  fun S _ _ hS hna heven σ hσ hout f D hD hDm _ => h S hS hna heven σ hσ hout f D hD hDm

theorem catSp6EvenOuter_of_catSp2mEvenOuter (h : CatSp2mEvenOuter 3) :
    F4Pilot.CatSp6EvenOuter :=
  fun S _ _ hS hna heven σ hσ hout f D hD hD6 hodd =>
    h S hS hna heven σ hσ hout f D hD hD6 hodd

theorem catSp2mEvenOuter_three_of_catSp6EvenOuter (h : F4Pilot.CatSp6EvenOuter) :
    CatSp2mEvenOuter 3 :=
  fun S _ _ hS hna heven σ hσ hout f D hD hD6 hodd =>
    h S hS hna heven σ hσ hout f D hD hD6 hodd

@[expose] def CatSp2mEvenOuterFamily (τ : StatedLieTag) (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n e : ℕ, StatedLieAdmissible τ n 2 e → LieModel S τ n 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp m 2 f →
      Sp2mOvergroupType S m f ∧ LieModel (fixedSubgroup σ) .PSp m 2 f

theorem catSp2mEvenOuterExact_of_families {m : ℕ} (h : ∀ τ, CatSp2mEvenOuterFamily τ m) :
    CatSp2mEvenOuterExact m := by
  intro S _ _ hS hna heven σ hσ hout f D hD hDm
  obtain ⟨τ, n, e, hadm, hmS⟩ := heven
  exact h τ S hS hna n e hadm hmS σ hσ hout f D hD hDm

theorem catSp2mEvenOuter_of_families {m : ℕ} (h : ∀ τ, CatSp2mEvenOuterFamily τ m) :
    CatSp2mEvenOuter m :=
  catSp2mEvenOuter_of_exact (catSp2mEvenOuterExact_of_families h)

theorem catSp2mEvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n e : ℕ, ¬ StatedLieAdmissible τ n 2 e) (m : ℕ) : CatSp2mEvenOuterFamily τ m :=
  fun _ _ _ _ _ n e hadm => absurd hadm (hτ n e)

theorem catSp2mEvenOuterFamily_POmegaOdd (m : ℕ) : CatSp2mEvenOuterFamily .POmegaOdd m :=
  catSp2mEvenOuterFamily_of_not_admissible (τ := .POmegaOdd) (fun _ _ hadm => hadm.2.2.2 rfl) m

theorem catSp2mEvenOuterFamily_twistedG2 (m : ℕ) : CatSp2mEvenOuterFamily .twistedG2 m :=
  catSp2mEvenOuterFamily_of_not_admissible (τ := .twistedG2)
    (fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)) m

theorem catSp2mEvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n e : ℕ), StatedLieAdmissible τ n 2 e → LieModel K τ n 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) (m : ℕ) :
    CatSp2mEvenOuterFamily τ m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout
  exact absurd (hτ S n e hadm hmS σ (hσ ▸ pow_orderOf_eq_one σ)) hout

theorem catSp6EvenOuterFamily_of_catSp2mEvenOuterFamily {τ : StatedLieTag}
    (h : CatSp2mEvenOuterFamily τ 3) : F4Pilot.CatSp6EvenOuterFamily τ :=
  fun S _ _ hS hna n e hadm hmS σ hσ hout f D hD hD6 _ =>
    h S hS hna n e hadm hmS σ hσ hout f D hD hD6

section SuzukiReeTits


theorem catSp2mEvenOuterFamily_twistedB2 (m : ℕ) : CatSp2mEvenOuterFamily .twistedB2 m := by
  refine catSp2mEvenOuterFamily_of_involutions_inner (τ := .twistedB2)
    (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem catSp2mEvenOuterFamily_twistedF4 (m : ℕ) : CatSp2mEvenOuterFamily .twistedF4 m := by
  refine catSp2mEvenOuterFamily_of_involutions_inner (τ := .twistedF4)
    (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSp2mEvenOuterFamily_Tits (m : ℕ) : CatSp2mEvenOuterFamily .Tits m := by
  refine catSp2mEvenOuterFamily_of_involutions_inner (τ := .Tits)
    (fun K _ n e hadm hmK => ?_) m
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSp2mEvenOuterExact_of_open_families {m : ℕ} (hPSL : CatSp2mEvenOuterFamily .PSL m)
    (hPSU : CatSp2mEvenOuterFamily .PSU m) (hPSp : CatSp2mEvenOuterFamily .PSp m)
    (hOp : CatSp2mEvenOuterFamily .POmegaPlus m) (hOm : CatSp2mEvenOuterFamily .POmegaMinus m)
    (hG2 : CatSp2mEvenOuterFamily .G2 m) (hF4 : CatSp2mEvenOuterFamily .F4 m)
    (hE6 : CatSp2mEvenOuterFamily .E6 m) (hE7 : CatSp2mEvenOuterFamily .E7 m)
    (hE8 : CatSp2mEvenOuterFamily .E8 m) (h2E6 : CatSp2mEvenOuterFamily .twistedE6 m)
    (h3D4 : CatSp2mEvenOuterFamily .trialityD4 m) : CatSp2mEvenOuterExact m := by
  apply catSp2mEvenOuterExact_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact catSp2mEvenOuterFamily_POmegaOdd m
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact catSp2mEvenOuterFamily_twistedB2 m
  · exact catSp2mEvenOuterFamily_twistedG2 m
  · exact catSp2mEvenOuterFamily_twistedF4 m
  · exact catSp2mEvenOuterFamily_Tits m

end SuzukiReeTits

end CFSG.SeitzReduction.SymplecticPilot
