module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitPSLCover
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.StandardRecognition
open scoped MatrixGroups

structure TBInputs : Prop where
  catalogU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome
  schreier : LocalAnalysis.ComponentInitial.SchreierFor Catalog
  classicalInvolution : ClassicalInvolutionTheoremModels
  propA : BurgoynePropA
  propB : BurgoynePropB
  propC : BurgoynePropC
  l34 : L34PumpUpExclusion
  solomon : SolomonSignalizerInput
  held : HeldTrivialMultiplier
  griessTable : GriessMultipliersAllModels
  griessCovers : GriessMultipliersCentralCovers

variable {X : Type} [Group X] [Finite X]

theorem TBSetting.not_mem_center (hX : TBSetting X) {δ : X} (hδ : orderOf δ = 2) :
    δ ∉ center X := by
  have := hX.simple
  refine not_mem_center_of_isSimpleGroup hX.nonab fun h => ?_
  rw [h, orderOf_one] at hδ
  exact absurd hδ (by norm_num)

theorem not_mem_pPrimeCore_of_orderOf_two {J : Type*} [Group J] [Finite J] {g : J}
    (hg : orderOf g = 2) : g ∉ pPrimeCore 2 J := by
  intro h
  have hd : orderOf (⟨g, h⟩ : pPrimeCore 2 J) ∣ Nat.card (pPrimeCore 2 J) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hg] at hd
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl hd (pPrimeCore_coprime_card (p := 2))

theorem center_coreQuotient_ne_bot {δ : X} (hδ : orderOf δ = 2) {J : Subgroup X}
    (hJδ : J ≤ centralizer ({δ} : Set X)) (hδJ : δ ∈ J) : center (J ⧸ pPrimeCore 2 J) ≠ ⊥ := by
  intro hbot
  have hmem : ((⟨δ, hδJ⟩ : J) : J ⧸ pPrimeCore 2 J) ∈ center (J ⧸ pPrimeCore 2 J) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJδ j.2))
  rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact not_mem_pPrimeCore_of_orderOf_two (by rw [Subgroup.orderOf_mk]; exact hδ) hmem

theorem center_coreQuotient_eq_bot_of_fusionZStar_eq (J : Type*) [Group J]
    (h : Open.fusionZStar J = pPrimeCore 2 J) : center (J ⧸ pPrimeCore 2 J) = ⊥ := by
  apply comap_injective (QuotientGroup.mk'_surjective (pPrimeCore 2 J))
  calc (center (J ⧸ pPrimeCore 2 J)).comap (QuotientGroup.mk' (pPrimeCore 2 J))
      = UnbalancingLocal.centralPreimage (pPrimeCore 2 J) := rfl
    _ = Open.fusionZStar J := (fusionZStar_eq_centralPreimage J).symm
    _ = pPrimeCore 2 J := h
    _ = (⊥ : Subgroup (J ⧸ pPrimeCore 2 J)).comap (QuotientGroup.mk' (pPrimeCore 2 J)) := by
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem intrinsic_config_types (hI : TBInputs) (hX : TBSetting X) {δ a : X} {J E : Subgroup X}
    (hC : IsUnbalancingConfig δ a J E) (hδJ : δ ∈ J) :
    (OddLieType (J ⧸ Open.fusionZStar J) ∧
        ∀ p f : ℕ, p.Prime → p ≠ 2 → ¬ LieModel (J ⧸ Open.fusionZStar J) .PSL 2 p f) ∨
      LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hX.simple
  obtain ⟨hδ, -, -, hJδ, hJ, -⟩ := id hC
  have hcen := center_coreQuotient_ne_bot hδ hJδ hδJ
  have hq := twoComponent_coreQuotient_quasisimple hJδ hJ
  have hZ2 := center_isPGroup_two_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    (Q := J ⧸ pPrimeCore 2 J)
  rcases config_uList hI.catalogU hX.kProper (hX.not_mem_center hδ) hC with
    hodd | ⟨n, hn, h7, ⟨e⟩⟩ | hL34 | hHe
  · by_cases hL2 : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel (J ⧸ Open.fusionZStar J) .PSL 2 p f
    · exfalso
      obtain ⟨p, f, hp, hp2, hm⟩ := hL2
      obtain ⟨hf, _, ⟨eSL⟩⟩ := psl_two_double_cover hI.griessTable hI.griessCovers hq hZ2 hcen hp
        hp2 (LieType.CurtisTits.lieModel_of_mulEquiv (coreQuotientCenterEquiv J).symm hm)
      exact intrinsic_SL2_exclusion hI.classicalInvolution hI.catalogU hX hδ hJδ hJ hδJ hp2 hf
        eSL
    · refine .inl ⟨hodd, fun p f hp hp2 hm => hL2 ⟨p, f, hp, hp2, hm⟩⟩
  · exact absurd (center_coreQuotient_eq_bot_of_fusionZStar_eq J
      (hI.solomon X hX.nonab hX.kProper hX.unbalanced hX.notU δ n J hδ hn h7 hJδ hJ ⟨e⟩)) hcen
  · exact .inr hL34
  · obtain ⟨e⟩ := hHe
    exact absurd (hI.held _ hq ⟨(coreQuotientCenterEquiv J).trans e⟩) hcen

end CFSG.ComponentClassification.TBLit
