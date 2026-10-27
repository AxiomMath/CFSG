module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatInputsSporadic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatInputs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

@[expose] def Sp2mOvergroup (K : Type) [Group K] (τ : MulAut K) (m f : ℕ) : Prop :=
  τ ∉ (MulAut.conj : K →* MulAut K).range ∧ Odd (Nat.card (center K)) ∧
    Sp2mOvergroupType (K ⧸ center K) m f ∧
    LieModel (fixedSubgroup (centerQuotientAut τ)) .PSp m 2 f

theorem sp2mOvergroup_three_iff {K : Type} [Group K] {τ : MulAut K} {f : ℕ} :
    Sp2mOvergroup K τ 3 f ↔ F4Pilot.Sp6Overgroup K τ f :=
  Iff.rfl

@[expose] def CatSp2mEvenInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → ∀ σ : MulAut S, orderOf σ = 2 → σ ∈ (MulAut.conj : S →* MulAut S).range →
    ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D → LieModel D .PSp m 2 f → False

@[expose] def Sp2mCatalogueClausesAt (m : ℕ) : Prop :=
  CatSp2mAlternating ∧ CatSp2mEvenInner ∧ CatSp2mEvenOuter m ∧ CatSp2mOddLie m ∧
    CatSp2mSporadic m ∧ CatSp2mCovers

@[expose] def Sp2mCatalogueClauses : Prop :=
  ∀ m : ℕ, 2 ≤ m → Sp2mCatalogueClausesAt m

@[expose] def Sp2mOvergroupCatalogue : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → Catalog (K ⧸ center K) →
    ∀ τ : MulAut K, orderOf τ = 2 → ∀ (m f : ℕ) (D : Subgroup (fixedSubgroup τ)),
      IsComponent D → LieModel D .PSp m 2 f → FixedCentralizerTwoFree τ D →
        Sp2mOvergroup K τ m f

theorem sp2m_simple_of_clauses {m : ℕ} (h : Sp2mCatalogueClausesAt m) {S : Type} [Group S]
    [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ} {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel D .PSp m 2 f) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range → FixedCentralizerTwoSmall σ D → False) ∧
      (FixedCentralizerTwoFree σ D →
        σ ∉ (MulAut.conj : S →* MulAut S).range ∧
          Sp2mOvergroupType S m f ∧ LieModel (fixedSubgroup σ) .PSp m 2 f) := by
  obtain ⟨hAlt, hEI, hEO, hOdd, hSpor, -⟩ := h
  have hcases := (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat
  refine ⟨fun hin hsmall => ?_, fun hodd => ?_⟩
  · rcases hcases with hA | ho | he | hsp
    · exact hAlt S hS hna hA σ hσ m f D hD hDm
    · exact hOdd S hS hna ho σ hσ f D hD hDm
    · exact hEI S hS hna he σ hσ hin m f D hD hDm
    · exact hSpor S hS hna hsp σ hσ f D hD hDm (.inl ⟨hin, hsmall⟩)
  · have hout := LinearPilot.not_mem_range_conj_of_twoFree hna hσ hodd
    refine ⟨hout, ?_⟩
    rcases hcases with hA | ho | he | hsp
    · exact (hAlt S hS hna hA σ hσ m f D hD hDm).elim
    · exact (hOdd S hS hna ho σ hσ f D hD hDm).elim
    · exact hEO S hS hna he σ hσ hout f D hD hDm hodd
    · exact (hSpor S hS hna hsp σ hσ f D hD hDm (.inr hodd)).elim

theorem sp2m_not_inner_of_clauses {m : ℕ} (h : Sp2mCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel D .PSp m 2 f) (hsmall : FixedCentralizerTwoSmall τ D) :
    τ ∉ (MulAut.conj : K →* MulAut K).range := fun hin => by
  obtain ⟨hτ', hinn, D', hD', hD'm, -, hsmall'⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  exact (sp2m_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hD' hD'm).1 (hinn hin)
    (hsmall' hin hsmall).2

theorem sp2m_overgroup_catalogue {m : ℕ} (h : Sp2mCatalogueClausesAt m) {K : Type} [Group K]
    [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) {f : ℕ} (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel D .PSp m 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    Sp2mOvergroup K τ m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, hodd', -⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  obtain ⟨hZ, hodd2⟩ := hodd' hodd
  obtain ⟨hout, htype, hfix⟩ := (sp2m_simple_of_clauses h hK.2.1 hK.2.2 hcat hτ' hD' hD'm).2 hodd2
  exact ⟨fun hin => hout (hinn hin), hZ, htype, hfix⟩

theorem sp2mOvergroupCatalogue_of_clauses (h : Sp2mCatalogueClauses) : Sp2mOvergroupCatalogue :=
  fun _ _ _ hK hcat τ hτ m _ D hD hDm hodd =>
    sp2m_overgroup_catalogue (h m (admissible_of_lieModel_PSp hDm).2.1) hK hcat τ hτ D hD hDm hodd

theorem catSp6EvenInner_of_catSp2mEvenInner (h : CatSp2mEvenInner) : F4Pilot.CatSp6EvenInner :=
  fun S _ _ hS hna heven σ hσ hin f D hD hD6 => h S hS hna heven σ hσ hin 3 f D hD hD6

theorem sp2mCatalogueClausesAt_three_of_sp6CatalogueClauses (h : F4Pilot.Sp6CatalogueClauses)
    (hAlt : CatSp2mAlternating) (hEI : CatSp2mEvenInner) (hCov : CatSp2mCovers) :
    Sp2mCatalogueClausesAt 3 :=
  ⟨hAlt, hEI, catSp2mEvenOuter_three_of_catSp6EvenOuter h.2.2.1, catSp6OddLie_iff.mpr h.2.2.2.1,
    catSp2mSporadic_three_of_catSp6Sporadic h.2.2.2.2.1, hCov⟩

end CFSG.SeitzReduction.SymplecticPilot
