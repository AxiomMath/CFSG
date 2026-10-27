module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.UnitaryPilot (CatSUmAlternating CatSUmEvenInner CatSUmEvenOuterAt
  CatSUmOddLieAt CatSUmSporadicAt CatSUmCovers SUmCatalogueClausesAt SUmSmall SUmOvergroup
  SUmNotOddLieInputAt)

@[expose] def CatSUmSporadicAtF (m f : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ D : Subgroup (fixedSubgroup σ), IsComponent D →
      LieModel (D ⧸ center D) .PSU m 2 f →
      ((σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D ∧
          Odd (Nat.card (center D))) ∨ FixedCentralizerTwoFree σ D) → m = 4 ∧ f = 1

theorem catSUmSporadicAt_iff {m : ℕ} : CatSUmSporadicAt m ↔ ∀ f, CatSUmSporadicAtF m f :=
  ⟨fun h f S _ _ hS hna hsp σ hσ D hD hDm hc => h S hS hna hsp σ hσ f D hD hDm hc,
    fun h S _ _ hS hna hsp σ hσ f D hD hDm hc => h f S hS hna hsp σ hσ D hD hDm hc⟩

@[expose] def SUmCatalogueClausesAtF (m f : ℕ) : Prop :=
  CatSUmAlternating ∧ CatSUmEvenInner ∧ CatSUmEvenOuterAt m ∧ CatSUmOddLieAt m ∧
    CatSUmSporadicAtF m f ∧ CatSUmCovers

theorem sum_simple_of_clausesF {m f : ℕ} (h : SUmCatalogueClausesAtF m f) {S : Type} [Group S]
    [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hm : 4 ≤ m) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSU m 2 f) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range → FixedCentralizerTwoSmall σ D →
        Odd (Nat.card (center D)) → SUmSmall S m f) ∧
      (FixedCentralizerTwoFree σ D →
        σ ∉ (MulAut.conj : S →* MulAut S).range ∧
          (LieModel S .PSL m 2 (2 * f) ∨ SUmSmall S m f)) := by
  obtain ⟨hAlt, hEI, hEO, hOdd, hSpor, -⟩ := h
  have hcases := (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat
  refine ⟨fun hin hsmall hZD => ?_, fun hodd => ?_⟩
  · rcases hcases with hA | ho | he | hsp
    · exact (hAlt S hS hna hA σ hσ m f D hm hD hDm).elim
    · obtain ⟨h4, h1⟩ := hOdd S hS hna ho σ hσ f D hD hDm
      exact ⟨h4, h1, .inl ho⟩
    · exact (hEI S hS hna he σ hσ hin m f D hD hDm).elim
    · obtain ⟨h4, h1⟩ := hSpor S hS hna hsp σ hσ D hD hDm (.inl ⟨hin, hsmall, hZD⟩)
      exact ⟨h4, h1, .inr hsp⟩
  · have hout := LinearPilot.not_mem_range_conj_of_twoFree hna hσ hodd
    refine ⟨hout, ?_⟩
    rcases hcases with hA | ho | he | hsp
    · exact (hAlt S hS hna hA σ hσ m f D hm hD hDm).elim
    · obtain ⟨h4, h1⟩ := hOdd S hS hna ho σ hσ f D hD hDm
      exact .inr ⟨h4, h1, .inl ho⟩
    · exact .inl (hEO S hS hna he σ hσ hout f D hD hDm hodd)
    · obtain ⟨h4, h1⟩ := hSpor S hS hna hsp σ hσ D hD hDm (.inr hodd)
      exact .inr ⟨h4, h1, .inr hsp⟩

theorem sum_overgroup_catalogueF {m f : ℕ} (h : SUmCatalogueClausesAtF m f) {K : Type}
    [Group K] [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) (hm : 4 ≤ m) (D : Subgroup (fixedSubgroup τ)) (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) (hodd : FixedCentralizerTwoFree τ D) :
    SUmOvergroup K τ m f := by
  obtain ⟨hτ', hinn, D', hD', hD'm, -, hodd', -⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  obtain ⟨hZ, hodd2⟩ := hodd' hodd
  obtain ⟨hout, hlist⟩ := (sum_simple_of_clausesF h hK.2.1 hK.2.2 hcat hτ' hm hD' hD'm).2 hodd2
  exact ⟨fun hin => hout (hinn hin), hZ, hlist⟩

theorem sum_not_inner_of_clausesF {m f : ℕ} (h : SUmCatalogueClausesAtF m f) {K : Type}
    [Group K] [Finite K] (hK : IsQuasisimple K) (hcat : Catalog (K ⧸ center K)) (τ : MulAut K)
    (hτ : orderOf τ = 2) (hm : 4 ≤ m) (hmf : (m, f) ≠ (4, 1)) (D : Subgroup (fixedSubgroup τ))
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSU m 2 f)
    (hZD : Odd (Nat.card (center D))) (hsmall : FixedCentralizerTwoSmall τ D) :
    τ ∉ (MulAut.conj : K →* MulAut K).range := by
  intro hin
  obtain ⟨hτ', hinn, D', hD', hD'm, hZD', -, hsmall'⟩ := h.2.2.2.2.2 K hK τ hτ m f D hD hDm
  obtain ⟨-, hs'⟩ := hsmall' hin hsmall
  exact UnitaryPilot.not_sumSmall_of_ne hmf
    ((sum_simple_of_clausesF h hK.2.1 hK.2.2 hcat hτ' hm hD' hD'm).1 (hinn hin) hs' (hZD' hZD))

theorem six_ne_four_one (f : ℕ) : ((6 : ℕ), f) ≠ (4, 1) := fun h => by
  have := congrArg Prod.fst h
  norm_num at this

end CFSG.SeitzReduction.TwistedE6Pilot
