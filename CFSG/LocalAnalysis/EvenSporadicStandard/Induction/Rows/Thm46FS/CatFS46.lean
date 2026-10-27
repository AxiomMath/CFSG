module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GrSLit (HeldNotProperFixedInput)
open CFSG.ComponentClassification.GrSLit.L34Sec5S (SuzONanNotProperFixedCatalog)

@[expose] def L3FixedCatalogGe3 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ x y : S, x * y ≠ y * x) → Catalog S → ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup S, P ≤ fixedSubgroup σ → IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) →
      P ≠ ⊤ → LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 n → LieModel S .PSL 3 2 (2 * n)

@[expose] def L34FixedCatalog : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) → Catalog S →
    ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup S, P ≤ fixedSubgroup σ → IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) →
      P ≠ ⊤ → LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 2 →
        Nonempty (S ≃* NativeSporadic.He) ∨ IsSporadic S .Suz ∨ IsSporadic S .ONan ∨
          LieModel S .PSL 3 2 4

@[expose] def Sol78Thm46SporL34Centre : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    ∀ σ : MulAut S, (∀ y, σ (σ y) = y) →
    ∀ Q : Subgroup S, Q ≤ fixedSubgroup σ → IsPComponent 2 (Q.subgroupOf (fixedSubgroup σ)) →
      Q ≠ ⊤ → Open.fusionZStar Q = center Q → LieModel (↥Q ⧸ center ↥Q) .PSL 3 2 2 →
        (IsSporadic S .Suz → LieModel ↥Q .PSL 3 2 2) ∧
          (Nonempty (S ≃* NativeSporadic.He) → IsKleinFour ↥(center ↥Q)) ∧
          (IsSporadic S .ONan → Nonempty (↥(center ↥Q) ≃* Multiplicative (ZMod 4)))

theorem sol78Thm46CatFS_of_inputs (hSuz : SuzONanNotProperFixedCatalog)
    (hHe : HeldNotProperFixedInput) (hL3 : L3FixedCatalogGe3) (hL34 : L34FixedCatalog)
    (hCen : Sol78Thm46SporL34Centre) : Sol78Thm46CatFS := by
  intro Y _ _ N' hF hidx hkp hcat P hP hPq hty hsuz
  obtain ⟨σ, Q, -, hσ, hle, -, hcomp, hne, hZ, ⟨e⟩⟩ := fixedComponent_of_solStd hF hidx hP hPq
  haveI := hF.isSimpleGroup
  have hna := hF.nonabelian
  have := hF.normal
  have hPN : P ≤ N' := Hyp.le_of_perfect_of_index_le_two hidx hPq.1
  rcases hty with ⟨n, hn, hL⟩ | hS | hHe'
  · have hLQ := lieModel_fusionZStar_of_solStd e hZ hL
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      have hLc : LieModel (↥Q ⧸ center ↥Q) .PSL 3 2 2 :=
        CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
          (CFSG.ComponentClassification.CatFC.quotientCenterEquiv e).symm hL
      rcases hL34 ↥N' hF.isSimpleGroup hna hcat σ hσ Q hle hcomp hne hLQ with
        hH | hSz | hON | hL316
      · have hc := (hCen ↥N' hF.isSimpleGroup hna σ hσ Q hle hcomp hne hZ
          hLc).2.1 hH
        obtain ⟨f⟩ := hc
        exact Or.inr (Or.inr (Or.inl ⟨⟨(Subgroup.centerCongr e).symm.trans f⟩, hL, hH⟩))
      · exact Or.inr (Or.inl ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e
          ((hCen ↥N' hF.isSimpleGroup hna σ hσ Q hle hcomp hne hZ hLc).1 hSz), hSz⟩)
      · obtain ⟨f⟩ := (hCen ↥N' hF.isSimpleGroup hna σ hσ Q hle hcomp hne hZ hLc).2.2 hON
        exact Or.inr (Or.inr (Or.inr ⟨⟨(Subgroup.centerCongr e).symm.trans f⟩, hL, hON, hPN⟩))
      · exact Or.inl ⟨2, le_rfl, hL316⟩
    · exact Or.inl ⟨n, by omega, hL3 n hn3 ↥N' hF.isSimpleGroup hna hcat σ hσ Q hle hcomp hne hLQ⟩
  · exact absurd (hSuz ↥N' hF.isSimpleGroup hna hcat σ hσ Q hle hcomp hne).1
      (not_not.2 (isSporadic_fusionZStar_of_solStd e hZ hS))
  · exact absurd (isSporadic_fusionZStar_of_solStd e hZ hHe') (hHe ↥N' hF.isSimpleGroup hna hcat
      σ hσ Q hle hcomp hne)

end CFSG.EvenSporadicStandard.Induction
