module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatFS412
public import CFSG.Sporadic.Schreier.TitsInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def G2EvenOuterFamily (τ : StatedLieTag) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (m f : ℕ), StatedLieAdmissible τ m 2 f → LieModel K τ m 2 f →
    ∀ α : MulAut K, orderOf α = 2 → α ∉ (MulAut.conj : K →* MulAut K).range →
    ∀ P : Subgroup (fixedSubgroup α), IsPComponent 2 P → ∀ n : ℕ,
      LieModel (P ⧸ Open.fusionZStar P) .G2 0 2 n → τ = .G2 ∧ f = 2 * n

theorem g2EvenOuterFixedCatalog_of_families (h : ∀ τ, G2EvenOuterFamily τ) :
    G2EvenOuterFixedCatalog := by
  intro n _ S _ _ _ hE σ hσ hout D hD hL
  obtain ⟨τ, m, f, hadm, hmS⟩ := hE
  have hP : IsPComponent 2 D :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hZD : Open.fusionZStar ↥D = center ↥D :=
    ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hD.1
      (ComponentClassification.CatLeaf.pPrimeCore_ne_top_of_isPComponent hP)
  obtain ⟨rfl, hf⟩ := h τ S m f hadm hmS σ hσ hout D hP n
    (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hZD).symm hL)
  obtain rfl : m = 0 := hadm.2.2.1
  rw [← hf]
  exact hmS

theorem g2EvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ m f : ℕ, ¬ StatedLieAdmissible τ m 2 f) : G2EvenOuterFamily τ :=
  fun _ _ _ m f hadm => absurd hadm (hτ m f)

theorem g2EvenOuterFamily_POmegaOdd : G2EvenOuterFamily .POmegaOdd :=
  g2EvenOuterFamily_of_not_admissible fun _ _ hadm => hadm.2.2.2 rfl

theorem g2EvenOuterFamily_twistedG2 : G2EvenOuterFamily .twistedG2 :=
  g2EvenOuterFamily_of_not_admissible fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)

theorem g2EvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (m f : ℕ), StatedLieAdmissible τ m 2 f → LieModel K τ m 2 f →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) :
    G2EvenOuterFamily τ := by
  intro K _ _ m f hadm hmK α hα hout
  exact absurd (hτ K m f hadm hmK α (hα ▸ pow_orderOf_eq_one α)) hout

section SuzukiReeTits


theorem g2EvenOuterFamily_twistedB2 : G2EvenOuterFamily .twistedB2 := by
  refine g2EvenOuterFamily_of_involutions_inner (τ := .twistedB2) fun K _ m f _ hmK => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f (Or.inl ?_)
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem g2EvenOuterFamily_twistedF4 : G2EvenOuterFamily .twistedF4 := by
  refine g2EvenOuterFamily_of_involutions_inner (τ := .twistedF4) fun K _ m f _ hmK => ?_
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f
    (Or.inr (Or.inl ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem g2EvenOuterFamily_Tits : G2EvenOuterFamily .Tits := by
  refine g2EvenOuterFamily_of_involutions_inner (τ := .Tits) fun K _ m f hadm hmK => ?_
  obtain rfl : f = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem g2EvenOuterFixedCatalog_of_open_families (hPSL : G2EvenOuterFamily .PSL)
    (hPSU : G2EvenOuterFamily .PSU) (hPSp : G2EvenOuterFamily .PSp)
    (hOp : G2EvenOuterFamily .POmegaPlus) (hOm : G2EvenOuterFamily .POmegaMinus)
    (hG2 : G2EvenOuterFamily .G2) (hF4 : G2EvenOuterFamily .F4)
    (hE6 : G2EvenOuterFamily .E6) (hE7 : G2EvenOuterFamily .E7)
    (hE8 : G2EvenOuterFamily .E8) (h2E6 : G2EvenOuterFamily .twistedE6)
    (h3D4 : G2EvenOuterFamily .trialityD4) : G2EvenOuterFixedCatalog := by
  apply g2EvenOuterFixedCatalog_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact g2EvenOuterFamily_POmegaOdd
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact g2EvenOuterFamily_twistedB2
  · exact g2EvenOuterFamily_twistedG2
  · exact g2EvenOuterFamily_twistedF4
  · exact g2EvenOuterFamily_Tits

end SuzukiReeTits

end CFSG.EvenSporadicStandard.Induction
