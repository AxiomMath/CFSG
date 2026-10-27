module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarSingleFacts
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatFiveMain
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenMGmat
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatFiveOut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineSixPairFiveDirect
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineSixPairFiveCatalogue
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixStarEGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.LocalAnalysis.AGL81I.Section3

theorem suzukiModel_of_isComponent_pair
    (hCat : CFSG.LocalAnalysis.AGL81I.Section3.Catalogue24_12Five)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hSporOut : ∀ s : TauCeti.SporadicName, Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.Blueprint.NativeSporadic.Carrier s)) ∣ 2)
    (hSporSimple : ∀ s : TauCeti.SporadicName,
      IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s))
    {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hσ : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hp5 : 5 ≤ p)
    {C C' : Subgroup (StarGroup p H)} (hC : CFSG.IsComponent C) (hC' : CFSG.IsComponent C')
    (hCC' : C ≠ C') (hCM : ¬ C ≤ starImg p H M) (hC'M : ¬ C' ≤ starImg p H M) :
    p = 5 ∧ CFSG.Blueprint.SuzukiModel ↥C 2 5 := by
  let N : Subgroup (StarGroup p H) := Subgroup.normalizer (C : Set (StarGroup p H))
  let e : ↥(C.subgroupOf N) ≃* ↥C :=
    Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := C))
  have hO : CFSG.pPrimeCore p (StarGroup p H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup h.prime
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 :=
    h.pRank_star_le_three hH2 hσ
  have hstep := pRank_add_one_le_of_ne_prime (X := StarGroup p H)
    (h.isKGroup_quotient p) h.prime h.ne_two hO hC' hC hCC'.symm
  have hrkC : CFSG.Open.pRank p C ≤ 2 :=
    Nat.succ_le_succ_iff.mp (hstep.trans hrank)
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥(C.subgroupOf N)) ≤ 2 :=
    calc CFSG.Open.pRank p (⊤ : Subgroup ↥(C.subgroupOf N))
        = CFSG.Open.pRank p (⊤ : Subgroup ↥C) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv h.prime.one_lt e
      _ = CFSG.Open.pRank p C :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup C).symm
      _ ≤ 2 := hrkC
  obtain ⟨hZ, hdis⟩ := pairFive_member_facts_of_mulEquiv e hC.1
    (pairFive_member_facts hSporOut hSporSimple hp5
      (kGroupLowRank24_12_subgroupOf_normalizer hCat hbridge h hH2 hσ hp5 hC hCM) hrk)
  rcases hdis with hSz | hout
  · exact hSz
  · exfalso
    exact false_of_pair_of_not_dvd_card_outer h.prime hrank hC hC' hCC' hZ
      (thc_dvd_card h.prime hO hC') (isElemAbelian_starImg_E_gen h) (card_starImg_E_gen h)
      (starImg_E_le_normalizer_gen h hC hCM) (starImg_E_le_normalizer_gen h hC' hC'M)
      (fun x hx hx1 => not_le_centralizer_of_mem_starImg_E_gen h hCM hx hx1)
      (fun x hx hx1 => not_le_centralizer_of_mem_starImg_E_gen h hC'M hx hx1) hout

theorem nineSixMoreoverPairFive_of_inputs
    (hCat : CFSG.LocalAnalysis.AGL81I.Section3.Catalogue24_12Five)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hSporOut : ∀ s : TauCeti.SporadicName, Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.Blueprint.NativeSporadic.Carrier s)) ∣ 2)
    (hSporSimple : ∀ s : TauCeti.SporadicName,
      IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s)) :
    NineSixMoreoverPairFive := by
  intro G _ _ M Q H E p h hH2 hσ hp3 L I hL hLM hI hIM hLI
  have hp5 : 5 ≤ p := by
    have hp2 : 2 ≤ p := h.prime.two_le
    have hpne2 : p ≠ 2 := h.ne_two
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd h.prime (by decide)
    omega
  have hLc : CFSG.IsComponent (starImg p H L) := isComponent_starImg hL
  have hIc : CFSG.IsComponent (starImg p H I) := isComponent_starImg hI
  have hne : starImg p H L ≠ starImg p H I := fun heq =>
    hLI (eq_of_starImg_eq h.prime hL hI heq)
  have hLM' : ¬ starImg p H L ≤ starImg p H M := fun hle =>
    hLM ((h.le_iff_starImg_le hL.1).mpr hle)
  have hIM' : ¬ starImg p H I ≤ starImg p H M := fun hle =>
    hIM ((h.le_iff_starImg_le hI.1).mpr hle)
  have h1 := suzukiModel_of_isComponent_pair hCat hbridge hSporOut hSporSimple h hH2 hσ
    hp5 hLc hIc hne hLM' hIM'
  have h2 := suzukiModel_of_isComponent_pair hCat hbridge hSporOut hSporSimple h hH2 hσ
    hp5 hIc hLc hne.symm hIM' hLM'
  exact ⟨h1.1, isoLie_suzuki_two_of_suzukiModel h1.2,
    isoLie_suzuki_two_of_suzukiModel h2.2⟩

theorem nineSixMoreoverPairFive_holds
    : NineSixMoreoverPairFive :=
  nineSixMoreoverPairFive_of_inputs
    (CFSG.LocalAnalysis.AGL81I.Section3.catalogue24_12Five_of_sporadicGen
      CFSG.LocalAnalysis.AGL81I.Section3.SporGen.MThirteen.sporadicGen24_12Five_holds)
    CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge
    (CFSG.AGLEmbedding.card_outer_carrier_dvd_two CFSG.Milestones.fam_m_simplicity)
    (fun s => (CFSG.Sporadic.Bridge.carrier_finite_simple CFSG.Milestones.fam_m_finiteness
      CFSG.Milestones.fam_m_simplicity s).2)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
