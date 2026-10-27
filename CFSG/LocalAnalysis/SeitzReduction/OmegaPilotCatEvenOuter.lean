module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatCovers
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem omegaTypeDet_of_simple {m : ℕ} (hdet : OmegaEvenTypeDetAt m) {D : Type} [Group D]
    (hq : IsQuasisimple D) (hsD : IsSimpleGroup D) {s : StatedLieTag}
    (hs : s = .POmegaPlus ∨ s = .POmegaMinus) {f : ℕ} (hDm : LieModel (D ⧸ center D) s m 2 f)
    {t : StatedLieTag} {n f' : ℕ} (hadm : StatedLieAdmissible t n 2 f')
    (hD : LieModel D t n 2 f') : t = s ∧ n = m ∧ f' = f :=
  hdet (D ⧸ center D) s f t n f' hs hDm hadm
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot
      (F4Pilot.center_eq_bot_of_isQuasisimple hq hsD) hD)

@[expose] def CatOmegaEvenOuterFamilyAt (τ : StatedLieTag) (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n e : ℕ, StatedLieAdmissible τ n 2 e → LieModel S τ n 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (t : StatedLieTag) (f : ℕ) (D : Subgroup (fixedSubgroup σ)),
      (t = .POmegaPlus ∨ t = .POmegaMinus) → IsComponent D →
      LieModel (D ⧸ center D) t m 2 f → FixedCentralizerTwoFree σ D →
        LieModel S .POmegaPlus m 2 (2 * f)

theorem catOmegaEvenOuterAt_of_families {m : ℕ} (h : ∀ τ, CatOmegaEvenOuterFamilyAt τ m) :
    CatOmegaEvenOuterAt m := by
  intro S _ _ hS hna heven σ hσ hout t f D ht hD hDm hodd
  obtain ⟨τ, n, e, hadm, hmS⟩ := heven
  exact h τ S hS hna n e hadm hmS σ hσ hout t f D ht hD hDm hodd

theorem catOmegaEvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n e : ℕ, ¬ StatedLieAdmissible τ n 2 e) (m : ℕ) : CatOmegaEvenOuterFamilyAt τ m :=
  fun _ _ _ _ _ n e hadm => absurd hadm (hτ n e)

theorem catOmegaEvenOuterFamily_POmegaOdd (m : ℕ) : CatOmegaEvenOuterFamilyAt .POmegaOdd m :=
  catOmegaEvenOuterFamily_of_not_admissible (τ := .POmegaOdd) (fun _ _ hadm => hadm.2.2.2 rfl) m

theorem catOmegaEvenOuterFamily_twistedG2 (m : ℕ) : CatOmegaEvenOuterFamilyAt .twistedG2 m :=
  catOmegaEvenOuterFamily_of_not_admissible (τ := .twistedG2)
    (fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)) m

theorem catOmegaEvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n e : ℕ), StatedLieAdmissible τ n 2 e → LieModel K τ n 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) (m : ℕ) :
    CatOmegaEvenOuterFamilyAt τ m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout
  exact absurd (hτ S n e hadm hmS σ (hσ ▸ pow_orderOf_eq_one σ)) hout

section SuzukiReeTits


theorem catOmegaEvenOuterFamily_twistedB2 (m : ℕ) : CatOmegaEvenOuterFamilyAt .twistedB2 m := by
  refine catOmegaEvenOuterFamily_of_involutions_inner (τ := .twistedB2)
    (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem catOmegaEvenOuterFamily_twistedF4 (m : ℕ) : CatOmegaEvenOuterFamilyAt .twistedF4 m := by
  refine catOmegaEvenOuterFamily_of_involutions_inner (τ := .twistedF4)
    (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catOmegaEvenOuterFamily_Tits (m : ℕ) : CatOmegaEvenOuterFamilyAt .Tits m := by
  refine catOmegaEvenOuterFamily_of_involutions_inner (τ := .Tits)
    (fun K _ n e hadm hmK => ?_) m
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catOmegaEvenOuterAt_of_open_families {m : ℕ} (hPSL : CatOmegaEvenOuterFamilyAt .PSL m)
    (hPSU : CatOmegaEvenOuterFamilyAt .PSU m) (hPSp : CatOmegaEvenOuterFamilyAt .PSp m)
    (hOp : CatOmegaEvenOuterFamilyAt .POmegaPlus m)
    (hOm : CatOmegaEvenOuterFamilyAt .POmegaMinus m)
    (hG2 : CatOmegaEvenOuterFamilyAt .G2 m) (hF4 : CatOmegaEvenOuterFamilyAt .F4 m)
    (hE6 : CatOmegaEvenOuterFamilyAt .E6 m) (hE7 : CatOmegaEvenOuterFamilyAt .E7 m)
    (hE8 : CatOmegaEvenOuterFamilyAt .E8 m) (h2E6 : CatOmegaEvenOuterFamilyAt .twistedE6 m)
    (h3D4 : CatOmegaEvenOuterFamilyAt .trialityD4 m) : CatOmegaEvenOuterAt m := by
  apply catOmegaEvenOuterAt_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact catOmegaEvenOuterFamily_POmegaOdd m
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact catOmegaEvenOuterFamily_twistedB2 m
  · exact catOmegaEvenOuterFamily_twistedG2 m
  · exact catOmegaEvenOuterFamily_twistedF4 m
  · exact catOmegaEvenOuterFamily_Tits m

end SuzukiReeTits

end CFSG.SeitzReduction.OmegaPilot
