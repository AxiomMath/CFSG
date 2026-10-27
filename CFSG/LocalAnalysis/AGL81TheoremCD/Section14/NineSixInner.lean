module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Cases
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34TypeCover
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStar
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStarE
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneInnerAction
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KSylowTwo
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL34
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6GInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Main
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeStar
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]
variable {M Q H E : Subgroup G}

theorem pow_three_eq_one_of_isLThreeFour_or_isSLThreeFour {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour Y ∨
      CFSG.LocalAnalysis.GLTheoremB.IsSLThreeFour Y)
    (hZ : Nat.card (Subgroup.center Y) ∣ 3) {k : Y} (hk : k ^ 3 ∈ Subgroup.center Y) :
    k ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hkP⟩ := IsPGroup.exists_le_sylow (p := 3)
    (isPGroup_zpowers_of_pow_three_mem_center hZ hk)
  have hkP' : k ∈ P := hkP (Subgroup.mem_zpowers k)
  rcases hY with hL3 | hSL3
  · have h3 := ((inputL34Facts_proved Y hL3).2 P).2.2 ⟨k, hkP'⟩
    simpa using h3
  · exact ((inputSL34Facts_proved Y hSL3).2 P).2.2 k hkP'

private theorem quotient_mul_conj_eq_of_commutator_mem {S : Type*} [Group S]
    {N : Subgroup S} [N.Normal] {T : Subgroup S} {e k : S}
    (h : ∀ y ∈ T, e * y * e⁻¹ * (k * y * k⁻¹)⁻¹ ∈ N) :
    ∀ w ∈ T.map (QuotientGroup.mk' N),
      QuotientGroup.mk' N e * w * (QuotientGroup.mk' N e)⁻¹ =
        QuotientGroup.mk' N k * w * (QuotientGroup.mk' N k)⁻¹ := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
  have hkey : QuotientGroup.mk' N (e * y * e⁻¹ * (k * y * k⁻¹)⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (h y hy)
  rw [← mul_inv_eq_one, ← hkey]
  simp only [map_mul, map_inv]

private theorem pow_three_mem_center_of_conj_eq {X : Type*} [Group X] {T : Subgroup X}
    {e k : X} (hkT : k ∈ T) (he3 : e ^ 3 = 1)
    (hrel : ∀ y ∈ T, e * y * e⁻¹ = k * y * k⁻¹) :
    (⟨k, hkT⟩ : T) ^ 3 ∈ Subgroup.center T := by
  let c : X := k⁻¹ * e
  have hc_cent : c ∈ Subgroup.centralizer (T : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcy : c * y = y * c := by
      calc c * y = k⁻¹ * (e * y) := by simp only [c]; group
        _ = k⁻¹ * ((e * y * e⁻¹) * e) := by group
        _ = k⁻¹ * ((k * y * k⁻¹) * e) := by rw [hrel y hy]
        _ = y * c := by simp only [c]; group
    exact hcy.symm
  have hkce : k * c = e := by simp only [c]; group
  have hck : Commute k c := Subgroup.mem_centralizer_iff.mp hc_cent k hkT
  have he3' : (k * c) ^ 3 = 1 := by rw [hkce]; exact he3
  have hcube : k ^ 3 * c ^ 3 = 1 := (hck.mul_pow 3).symm.trans he3'
  have hk3 : k ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hcube
  have hc3_cent : c ^ 3 ∈ Subgroup.centralizer (T : Set X) :=
    Subgroup.pow_mem _ hc_cent 3
  have hk3_cent : k ^ 3 ∈ Subgroup.centralizer (T : Set X) := by
    rw [hk3]
    exact Subgroup.inv_mem _ hc3_cent
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp hk3_cent (g : X) g.2

private theorem isL34Type_and_center_dvd_of_mulEquiv {Y Z : Type*} [Group Y] [Group Z]
    (e : Y ≃* Z) (hY : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour Y ∨
      CFSG.LocalAnalysis.GLTheoremB.IsSLThreeFour Y)
    (hZ : Nat.card (Subgroup.center Y) ∣ 3) :
    (CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour Z ∨
      CFSG.LocalAnalysis.GLTheoremB.IsSLThreeFour Z) ∧
      Nat.card (Subgroup.center Z) ∣ 3 := by
  refine ⟨hY.imp
    (CFSG.HardMathSupport.Solomon.Coordinator.i271h_isLThreeFour_of_mulEquiv e)
    (CFSG.HardMathSupport.Solomon.Coordinator.i271h_isSLThreeFour_of_mulEquiv e), ?_⟩
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  exact hZ

private theorem exists_inner_starImg_of_commutator
    (h : NineSettingGen G M 3 Q H E 2) {L : Subgroup G} (hLH : IsPComponentIn 3 L H)
    (hbar : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour (threeStar L) ∨
      CFSG.LocalAnalysis.GLTheoremB.IsSLThreeFour (threeStar L))
    (hcard : Nat.card (Subgroup.center (threeStar L)) ∣ 3)
    (hinner : ∀ b ∈ E, ∃ k ∈ L, ∀ y ∈ L,
      b * y * b⁻¹ * (k * y * k⁻¹)⁻¹ ∈ CFSG.Open.GLAPPrimeCoreOf 3 L) :
    ∀ e ∈ starImg 3 H E, ∃ k ∈ starImg 3 H L, k ^ 3 = 1 ∧
      ∀ y ∈ starImg 3 H L, e * y * e⁻¹ = k * y * k⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGLA : GLAPComponent 3 H L :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
      Nat.prime_three).2 hLH
  have hcoreL : CFSG.Open.GLAPPrimeCoreOf 3 L ≤ CFSG.Open.GLAPPrimeCoreOf 3 H :=
    CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three
      hGLA.2.1
  obtain ⟨e0⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hLH
  obtain ⟨hbar', hcard'⟩ := isL34Type_and_center_dvd_of_mulEquiv e0 hbar hcard
  intro e he
  obtain ⟨bH, hbE', rfl⟩ := Subgroup.mem_map.mp he
  have hbE : (bH : G) ∈ E := Subgroup.mem_subgroupOf.mp hbE'
  obtain ⟨k, hkL, hkcomm⟩ := hinner (bH : G) hbE
  let kH : ↥H := ⟨k, hLH.1 hkL⟩
  let kbar : StarGroup 3 H :=
    QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) kH
  have hkbar_mem : kbar ∈ starImg 3 H L :=
    Subgroup.mem_map.mpr ⟨kH, Subgroup.mem_subgroupOf.mpr hkL, rfl⟩
  have hcommN : ∀ y ∈ L.subgroupOf H,
      bH * y * bH⁻¹ * (kH * y * kH⁻¹)⁻¹ ∈ primeComplementCore (G := ↥H) 3 := by
    intro y hy
    have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hmem : (bH : G) * (y : G) * (bH : G)⁻¹ *
        (k * (y : G) * k⁻¹)⁻¹ ∈ CFSG.Open.GLAPPrimeCoreOf 3 H :=
      hcoreL (hkcomm (y : G) hyL)
    have hmem' : H.subtype (bH * y * bH⁻¹ * (kH * y * kH⁻¹)⁻¹) ∈
        CFSG.Open.GLAPPrimeCoreOf 3 H := by
      simpa [kH, CFSG.Open.GLAPPrimeCoreOf, CFSG.Open.GLAPPrimeCore] using hmem
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).mp hmem'
  have hact : ∀ w ∈ starImg 3 H L,
      QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) bH * w *
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) bH)⁻¹ =
      kbar * w * kbar⁻¹ := by
    have h := quotient_mul_conj_eq_of_commutator_mem (N := primeComplementCore (G := ↥H) 3)
      (T := L.subgroupOf H) (e := bH) (k := kH) hcommN
    simpa [kbar, starImg] using h
  have hb3 : bH ^ 3 = 1 := by
    exact Subtype.ext (h.stdE.2.2.1.2 (bH : G) hbE)
  have he3 : (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3) bH) ^ 3 = 1 := by
    rw [← map_pow, hb3, map_one]
  have hcube : (⟨kbar, hkbar_mem⟩ : ↥(starImg 3 H L)) ^ 3 ∈
      Subgroup.center ↥(starImg 3 H L) :=
    pow_three_mem_center_of_conj_eq hkbar_mem he3 hact
  have hkbar3 : kbar ^ 3 = 1 := by
    have h := pow_three_eq_one_of_isLThreeFour_or_isSLThreeFour hbar' hcard' hcube
    simpa using congrArg Subtype.val h
  exact ⟨kbar, hkbar_mem, hkbar3, hact⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen

open CFSG.LocalAnalysis.AGL81TheoremCD.Section14
open CFSG.Open

variable {G : Type} [Group G] [Finite G]
variable {M Q H E : Subgroup G}

theorem exists_inner_starImg
    (h : NineSettingGen G M 3 Q H E 2) (hple : ¬ pLayerIn 3 H ≤ M) {L : Subgroup G}
    (hL : CFSG.LocalAnalysis.AGL81TheoremCD.Section14.IsKComp M H L)
    (hL34 : IsL34Type (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.threeStar L)) :
    ∀ e ∈ starImg 3 H E, ∃ k ∈ starImg 3 H L, k ^ 3 = 1 ∧
      ∀ y ∈ starImg 3 H L, e * y * e⁻¹ = k * y * k⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLH : IsPComponentIn 3 L H := hL.isPComponentIn
  have hLM : ¬ L ≤ M := hL.not_le_M hple
  have hGLA : GLAPComponent 3 H L :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
      Nat.prime_three).2 hLH
  have hbar : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.threeStar L) ∨
      CFSG.LocalAnalysis.GLTheoremB.IsSLThreeFour
        (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.threeStar L) :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.isLThreeFour_or_isSLThreeFour_of_isL34Type
      hL.isQuasisimple (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three) hL34
  have hcard : Nat.card (Subgroup.center
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.threeStar L)) ∣ 3 :=
    hL.card_center_threeStar_dvd_three hL34
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    h.E_le_normalizer_of_isPComponentIn hLH hLM
  have hEH : E ≤ H := h.stdE.2.1.trans h.Q_le_H
  rcases CFSG.HardMathSupport.Solomon.UniquenessMaximal.input23_20_proved
    G H L E hGLA hbar hEH h.stdE.2.2.1 hEN with hle | ⟨hinn, -⟩
  · have hcoreH : CFSG.Open.GLAPPrimeCoreOf 3 H ≤ M := by
      have h := (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.pPrimeCore_map_le_relPPrimeCore
        (p := 3) (K := H) (H := H) le_rfl Subgroup.le_normalizer).trans h.relPPrimeCore_le
      simpa only [CFSG.Open.GLAPPrimeCoreOf, CFSG.Open.GLAPPrimeCore] using h
    refine absurd (hle.trans (sup_le ?_ ?_)) hLM
    · exact CFSG.LocalAnalysis.AGL81TheoremCD.Section14.gammaClBelow_le_of_rankThreeGamma_le
        h.stdE.2.2.1 h.stdE.2.2.2.1 (by simpa using h.stdE.2.2.2.2) L
    · exact (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three
        hGLA.2.1).trans hcoreH
  · exact exists_inner_starImg_of_commutator h hLH hbar hcard hinn

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen
