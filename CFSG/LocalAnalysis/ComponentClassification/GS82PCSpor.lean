module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporJ2
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporM12
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporTop
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadic
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Blueprint PCSpor
open CFSG.RankThree.PartTwo.Sec4.Census (sporadicMultiplierOrder)

theorem typPumpLeaf_spor_holds :
    TypPumpLeaf TypLeafSpor := by
  intro Y _ _ hq hO hZ ⟨s, ⟨e⟩⟩ β hβ T hTF hT hZT hC
  have h : Setting Y β T := ⟨hq, hO, hβ, hTF, hT, hZT, hC⟩
  have hMcard := Open.Open.monster_y443_derived_card
  by_cases hTtop : T = ⊤
  · exact false_of_top (AGLEmbedding.card_carrier_eq_sporOrd hMcard) h hTtop e
  have hdvd : Nat.card (center Y) ∣ sporadicMultiplierOrder s :=
    EvenSporadicStandard.Induction.card_center_dvd_of_sporadicMultipliers
      RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
      (Sporadic.Bridge.nonempty_carrier_mulEquiv_group s) hq ⟨e⟩
  obtain ⟨k, hk⟩ := (isPGroup_center_of_pPrimeCore_eq_bot hO).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hZ (Subgroup.eq_bot_of_card_eq _ hk)
  have h2 : 2 ∣ Nat.card (center Y) := hk ▸ dvd_pow_self 2 hk0
  have hZ2 : sporadicMultiplierOrder s ∣ 6 → Nat.card (center Y) = 2 := by
    intro h6
    have h1 : 2 ^ k ∣ 6 := hk ▸ hdvd.trans h6
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := this.trans h1
      norm_num at this
    rw [hk]
    interval_cases k
    · exact absurd rfl hk0
    · rfl
  have hGA := TBLit.griessMultipliersAllModels_holds
  have hGC := RankThree.PartTwo.Sec4.Census.griessMultipliersCentralCovers
  cases s
  case M12 => exact false_of_m12 h hTtop (hZ2 (by decide)) e
  case M22 => exact false_of_m22 hGA hGC CatalogueU.sporadicOddCoreFree_M22 h hTtop e
  case J2 => exact false_of_j2 hGA hGC CatalogueU.sporadicOddCoreFree_J2 h hTtop (hZ2 (by decide)) e
  case HS =>
    exact false_of_hs hMcard hGA hGC CatalogueU.sporadicOddCoreFree_HS h hTtop (hZ2 (by decide)) e
  case Suz =>
    exact false_of_suz hMcard CatalogueU.sporadicOddCoreFree_Suz h hTtop (hZ2 (by decide)) e
  case Ru => exact false_of_ru hMcard CatalogueU.sporadicOddCoreFree_Ru h hTtop e
  case Co1 => exact false_of_co1 hMcard CatalogueU.sporadicOddCoreFree_Co1 h hTtop e
  case Fi22 => exact false_of_fi22 hMcard CatalogueU.sporadicOddCoreFree_Fi22 h hTtop e
  case B => exact false_of_b hMcard BMCase.sporadicOddCoreFree_B h hTtop e
  all_goals
    have h3 := h2.trans hdvd
    simp [sporadicMultiplierOrder] at h3

end CFSG.ComponentClassification.GS82PumpInputs
