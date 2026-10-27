module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.ComponentStep
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.EBarTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.RowDispatch
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.MTypeOfE
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.MTypeSchur

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.ComponentClassification.HarrisLit

theorem false_of_isSubnormal_core (hH : Harris82Theorem1KProper)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersOdd)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : HRSetting G L) {z : G}
    {K : Subgroup G} (h : Case3Core G z K)
    (hsub : (K.subgroupOf (centralizer ({z} : Set G))).IsSubnormal) : False := by
  haveI : IsSimpleGroup G := hS.std.simple
  have hperf : Group.IsPerfect ↥K := h.quasisimple.1
  have hcore : CFSG.oddCore ↥K = CFSG.pPrimeCore 2 ↥K := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pPrimeCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hcore) h.quotient.1
  have hL : IsTwoComponentIn K (centralizer ({z} : Set G)) :=
    ⟨h.le_centralizer, hsub, hperf, hq⟩
  exact (not_isMTypeSchur_of_kProper hH hS.std.nonab hS.std.kProper hS.notCat h.orderOf_eq
    hL h.mem Nat.prime_three (by norm_num)) (isMTypeSchur_of_isSU43 hGA hperf h.quotient)

theorem isKGroupCat_centralizer_of_kProper {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {z : G} (hz : orderOf z = 2) :
    CFSG.SectionRank.IsKGroupCat ↥(centralizer ({z} : Set G)) :=
  CFSG.GH74.GLS.isKGroupNative_of_kProper hK
    (CFSG.GH74.GLS.centralizer_involution_ne_top (G := G) inferInstance hna hz)

theorem case3_false (hH : Harris82Theorem1KProper)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersOdd)
    (hI31 : CFSG.ASVolI.I_3_1) (hRows : Case3RowCores)
    (hM11 : Nat.card ↥CFSG.Blueprint.NativeSporadic.M11 = 7920) (hD : PSLUnitU43Leaf)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : HRSetting G L) {z : G}
    {K : Subgroup G} (h : Case3Core G z K) : False := by
  haveI : IsSimpleGroup G := hS.std.simple
  have hX : CFSG.SectionRank.IsKGroupCat ↥(centralizer ({z} : Set G)) :=
    isKGroupCat_centralizer_of_kProper hS.std.nonab hS.std.kProper h.orderOf_eq
  have hO : CFSG.oddCore ↥(centralizer ({z} : Set G)) = ⊥ := hS.balanced z h.orderOf_eq
  obtain ⟨E, hKE, hEz, hE, hEsub⟩ :=
    Case3Core.exists_component_ge hI31 h hX hO
  by_cases hKeq : K = E
  · subst E
    exact false_of_isSubnormal_core hH hGA hS h hEsub
  · obtain ⟨t, J, ht, hJC, hJs, htJ, hJq, hJ2, hJU, hJZ, he⟩ :=
      Case3Core.exists_ebar_data h hKE hEz hE hKeq
    haveI : IsSimpleGroup (↥E ⧸ center ↥E) := hE.2.1
    have hna : ∃ a b : ↥E ⧸ center ↥E, a * b ≠ b * a := hE.2.2
    have hcat : CFSG.Blueprint.Catalog (↥E ⧸ center ↥E) := by
      let φ : E.subgroupOf (centralizer ({z} : Set G)) →* (↥E ⧸ center ↥E) :=
        (QuotientGroup.mk' (center ↥E)).comp
          (Subgroup.subgroupOfEquivOfLe hEz).toMonoidHom
      have hφ : Function.Surjective φ := by
        intro s
        obtain ⟨e, he⟩ := QuotientGroup.mk'_surjective (center ↥E) s
        refine ⟨(Subgroup.subgroupOfEquivOfLe hEz).symm e, ?_⟩
        change QuotientGroup.mk' (center ↥E)
          ((Subgroup.subgroupOfEquivOfLe hEz)
            ((Subgroup.subgroupOfEquivOfLe hEz).symm e)) = s
        rw [MulEquiv.apply_symm_apply, he]
      exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hX
        (E.subgroupOf (centralizer ({z} : Set G))) φ hφ
    have hM : IsMTypeSchur 3 ↥K := isMTypeSchur_of_isSU43 hGA h.quasisimple.1 h.quotient
    have hI : T1.InductionTypeField 3 ↥K := inductionTypeField_of_isSU43 h.quotient
    have hL3 : T1.LieChar 3 (↥E ⧸ center ↥E) :=
      Case3RowCores.lieChar_three hRows hM11 hna hcat ht hJC hJs htJ hJ2 hM hI he hJU
    have hzE_center : (⟨z, hKE h.mem⟩ : ↥E) ∈ center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hEz y.2))
    have hzEord : orderOf (⟨z, hKE h.mem⟩ : ↥E) = 2 := by
      rw [Subgroup.orderOf_mk, h.orderOf_eq]
    have h2dvd : 2 ∣ Nat.card ↥(center ↥E) := by
      have := Subgroup.orderOf_dvd_natCard (center ↥E) hzE_center
      rwa [hzEord] at this
    have hev : Even (Nat.card ↥(center ↥E)) := even_iff_two_dvd.mpr h2dvd
    have hc : ∀ n r : ℕ, 0 < n → 0 < r →
        ¬ (CFSG.Blueprint.LieModel (↥E ⧸ center ↥E) .PSL (2 * n) 3 r ∨
          CFSG.Blueprint.LieModel (↥E ⧸ center ↥E) .PSU (2 * n) 3 r) := by
      intro n r hn hr hmodel
      obtain ⟨x, hx, hxord⟩ :=
        hD (↥E ⧸ center ↥E) n r hn hr hmodel t ht J hJC hJs htJ hJq hJU
      exact hJZ x hx hxord
    have hME : IsMTypeSchur 3 ↥E := isMTypeSchur_three_of_lieChar hE hev hL3 hc
    have h2E : 2 ∣ Nat.card ↥E := h2dvd.trans (Subgroup.card_subgroup_dvd_card (center ↥E))
    have hE2 : IsTwoQuasisimple ↥E :=
      (CFSG.ComponentClassification.HarrisLit.P1.isTwoQuasisimple_of_isQuasisimple hE h2E).1
    have hL : IsTwoComponentIn E (centralizer ({z} : Set G)) := ⟨hEz, hEsub, hE2⟩
    exact (not_isMTypeSchur_of_kProper hH hS.std.nonab hS.std.kProper hS.notCat h.orderOf_eq
      hL (hKE h.mem) Nat.prime_three (by norm_num)) hME

theorem g23StandardFalse_of_core (hH : Harris82Theorem1KProper)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersOdd)
    (hI31 : CFSG.ASVolI.I_3_1) (hRows : Case3RowCores)
    (hM11 : Nat.card ↥CFSG.Blueprint.NativeSporadic.M11 = 7920) (hD : PSLUnitU43Leaf)
    (hY : YamadaCase3Core) : CFSG.OddStandard.HigherRank.G23StandardFalse := by
  intro G _ _ L hS hL
  obtain ⟨z, K, h⟩ := hY G L hS hL
  exact case3_false hH hGA hI31 hRows hM11 hD hS h

end CFSG.OddStandard.HigherRank.G2Three
