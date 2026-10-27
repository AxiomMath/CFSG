module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Fixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def G2FixedCatalog : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ x y : S, x * y ≠ y * x) → Catalog S → ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup S, P ≤ fixedSubgroup σ → CFSG.IsComponent (P.subgroupOf (fixedSubgroup σ)) →
      P ≠ ⊤ → LieModel (P ⧸ Open.fusionZStar P) .G2 0 2 n →
        LieModel S .G2 0 2 (2 * n) ∨ (n = 2 ∧ IsSporadic S .Co1)

@[expose] def G2EvenOuterFixedCatalog : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → EvenLieType S →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ D : Subgroup ↥(fixedSubgroup σ), CFSG.IsComponent D →
      LieModel (↥D ⧸ center ↥D) .G2 0 2 n → LieModel S .G2 0 2 (2 * n)

@[expose] def Co1G24Centre : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ Q : Subgroup S, Q ≤ fixedSubgroup σ → IsPComponent 2 (Q.subgroupOf (fixedSubgroup σ)) →
      Q ≠ ⊤ → Open.fusionZStar Q = center Q → LieModel (↥Q ⧸ center ↥Q) .G2 0 2 2 →
        IsSporadic S .Co1 → LieModel ↥Q .G2 0 2 2

theorem sol78Thm412CatFS_of_inputs (hG2 : G2FixedCatalog) (hCo1 : Co1G24Centre) :
    Sol78Thm412CatFS := by
  intro Y _ _ N' hF hidx hkp hcat P hP hPq ⟨n, hn, hL⟩
  obtain ⟨σ, Q, -, hσ, hle, hcomp, hcomp2, hne, hZ, ⟨e⟩⟩ := fixedComponent_of_solStd hF hidx hP hPq
  haveI := hF.isSimpleGroup
  have hna := hF.nonabelian
  have hLQ := lieModel_fusionZStar_of_solStd e hZ hL
  rcases hG2 n hn ↥N' hF.isSimpleGroup hna hcat σ hσ Q hle hcomp hne hLQ with hS | ⟨rfl, hCo⟩
  · exact Or.inl ⟨n, hn, hS⟩
  · have hLc : LieModel (↥Q ⧸ center ↥Q) .G2 0 2 2 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (CFSG.ComponentClassification.CatFC.quotientCenterEquiv e).symm hL
    exact Or.inr ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e
      (hCo1 ↥N' hF.isSimpleGroup hna σ hσ Q hle hcomp2 hne hZ hLc hCo), hCo⟩

end CFSG.EvenSporadicStandard.Induction
