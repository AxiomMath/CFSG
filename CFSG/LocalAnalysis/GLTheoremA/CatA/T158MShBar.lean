module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Inn
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevAutFieldGraph
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Setup
public import CFSG.GroupTheory.SupCommute
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import TauCeti.GroupTheory.ExponentPrime
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Alpha
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem chevAut_eq_one_of_mem_centralizer {p : ℕ} (hp : p.Prime) {X L : Subgroup G} {g : G}
    (hL : GLAPComponent p X L) (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hcen : g ∈ Subgroup.centralizer (L : Set G)) :
    chevAut p L ⟨g, hgN⟩ = 1 := by
  rw [chevAut_eq_one_iff hp hL hgN]
  exact centMod_of_mem_centralizer hcen

theorem zpowers_sup_inf_centralizer_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K B L₁ L₂ : Subgroup G} {d b : G}
    (hL1 : GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set G)) L₁)
    (hL2 : GLAPComponent p (K ⊓ Subgroup.centralizer ({b} : Set G)) L₂)
    (hB : IsElemAbelian p B) (hdB : d ∈ B) (hbB : b ∈ B)
    (hdp : d ^ p = 1) (hbp : b ^ p = 1)
    (hfd : FGOn p d L₂) (hfb : FGOn p b L₁) :
    (Subgroup.zpowers d ⊔ Subgroup.zpowers b) ⊓
      (B ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  rintro z ⟨hzH, hzW⟩
  obtain ⟨hzB, hzC⟩ := Subgroup.mem_inf.1 hzW
  have hcomm : ∀ a ∈ Subgroup.zpowers d, ∀ c ∈ Subgroup.zpowers b, Commute a c := by
    intro a ha c hc
    exact isElemAbelian_commute hB (Subgroup.zpowers_le.2 hdB ha)
      (Subgroup.zpowers_le.2 hbB hc)
  obtain ⟨a, ha, c, hc, hzc⟩ := (CFSG.mem_sup_of_commute hcomm).1 hzH
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hdCenL1 : d ∈ Subgroup.centralizer (L₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (hL1.1 hl)).2
  have hbCenL2 : b ∈ Subgroup.centralizer (L₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (hL2.1 hl)).2
  have hCL1 : Subgroup.centralizer (K : Set G) ≤ Subgroup.centralizer (L₁ : Set G) :=
    Subgroup.centralizer_le (hL1.1.trans inf_le_left)
  have hCL2 : Subgroup.centralizer (K : Set G) ≤ Subgroup.centralizer (L₂ : Set G) :=
    Subgroup.centralizer_le (hL2.1.trans inf_le_left)
  have hev1 : Even (Nat.card (PSimple p L₁)) := by
    have hq : CFSG.Open.IsQuasisimple (PQuot p L₁) := isQuasisimple_pQuot_of_glaPComponent hp hL1
    exact even_iff_two_dvd.2 (CFSG.LocalAnalysis.GLTheoremA.I113.two_dvd_card_of_quasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_quotient_center hq))
  have hev2 : Even (Nat.card (PSimple p L₂)) := by
    have hq : CFSG.Open.IsQuasisimple (PQuot p L₂) := isQuasisimple_pQuot_of_glaPComponent hp hL2
    exact even_iff_two_dvd.2 (CFSG.LocalAnalysis.GLTheoremA.I113.two_dvd_card_of_quasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_quotient_center hq))
  have hbjCen : b ^ j ∈ Subgroup.centralizer (L₁ : Set G) := by
    have h1 : (d ^ i)⁻¹ * (d ^ i * b ^ j) ∈ Subgroup.centralizer (L₁ : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hdCenL1 i))
        (by rw [hzc]; exact hCL1 hzC)
    rwa [inv_mul_cancel_left] at h1
  have hbjeq : b ^ j = 1 := by
    by_cases hbj : b ^ j = 1
    · exact hbj
    · exfalso
      have hzy : Subgroup.zpowers (b ^ j) = Subgroup.zpowers b :=
        TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hbp hbj
          (Subgroup.zpow_mem_zpowers b j)
      have hbCen : b ∈ Subgroup.centralizer (L₁ : Set G) :=
        Subgroup.zpowers_le.2 hbjCen (by rw [hzy]; exact Subgroup.mem_zpowers b)
      have hbN : b ∈ Subgroup.normalizer (L₁ : Set G) :=
        Subgroup.centralizer_le_normalizer _ hbCen
      exact chevAut_ne_one_of_fgOn hp hp2 hbN hev1 hfb
        (chevAut_eq_one_of_mem_centralizer hp hL1 hbN hbCen)
  have hzdi : z = d ^ i := by rw [← hzc, hbjeq, mul_one]
  have hdiCen : d ^ i ∈ Subgroup.centralizer (L₂ : Set G) := by
    rw [← hzdi]
    exact hCL2 hzC
  have hdieq : d ^ i = 1 := by
    by_cases hdi : d ^ i = 1
    · exact hdi
    · exfalso
      have hzy : Subgroup.zpowers (d ^ i) = Subgroup.zpowers d :=
        TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hdp hdi
          (Subgroup.zpow_mem_zpowers d i)
      have hdCen : d ∈ Subgroup.centralizer (L₂ : Set G) :=
        Subgroup.zpowers_le.2 hdiCen (by rw [hzy]; exact Subgroup.mem_zpowers d)
      have hdN : d ∈ Subgroup.normalizer (L₂ : Set G) :=
        Subgroup.centralizer_le_normalizer _ hdCen
      exact chevAut_ne_one_of_fgOn hp hp2 hdN hev2 hfd
        (chevAut_eq_one_of_mem_centralizer hp hL2 hdN hdCen)
  rw [Subgroup.mem_bot]
  calc z = d ^ i * b ^ j := hzc.symm
    _ = 1 := by rw [hdieq, hbjeq, mul_one]

theorem barX_inf_centModSubgroup {p : ℕ} (hp : p.Prime) {C K B : Subgroup G}
    (hKC : K ≤ C) (hsn : IsSubnormal K C)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    barX p C (B ⊓ centModSubgroup p K) =
      barX p C B ⊓ Subgroup.centralizer
        (barX p C K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  have hmono : barX p C (B ⊓ centModSubgroup p K) ≤ barX p C B :=
    CFSG.LocalAnalysis.GLTheoremA.K156.barX_mono (p := p) (X := C) inf_le_left
  refine le_antisymm ?_ ?_
  · intro z hz
    refine Subgroup.mem_inf.2 ⟨hmono hz, ?_⟩
    refine barX_le_centralizer (p := p) (C := C) (S := B ⊓ centModSubgroup p K) (T := K) ?_ hz
    rintro s ⟨hsB, hscm⟩ t ht _ _
    have hts : ⁅t, s⁆ ∈ GLAPPrimeCoreOf p K := hscm.2 t ht
    have hmem : ⁅t, s⁆ ∈ GLAPPrimeCoreOf p C :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hsn hts
    have hEq : s * t * s⁻¹ * t⁻¹ = ⁅t, s⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hEq]
    exact Subgroup.inv_mem _ hmem
  · rintro z ⟨hzB, hzC⟩
    obtain ⟨bC, hbC, rfl⟩ := Subgroup.mem_map.1 hzB
    have hbB : (bC : G) ∈ B := Subgroup.mem_subgroupOf.1 hbC
    have hbK : (bC : G) ∈ Subgroup.normalizer (K : Set G) := hBN hbB
    refine Subgroup.mem_map.2 ⟨bC, Subgroup.mem_subgroupOf.2 ⟨hbB, ?_⟩, rfl⟩
    refine mem_centModSubgroup.2 ⟨hbK, fun k hk => ?_⟩
    have hkC : (⟨k, hKC hk⟩ : ↥C) ∈ (K.subgroupOf C) := Subgroup.mem_subgroupOf.2 hk
    have hmemK : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) ⟨k, hKC hk⟩ ∈ barX p C K :=
      ⟨⟨k, hKC hk⟩, hkC, rfl⟩
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) bC *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) ⟨k, hKC hk⟩ =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) ⟨k, hKC hk⟩ *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) bC :=
      ((Subgroup.mem_centralizer_iff.1 hzC) _ hmemK).symm
    have hu : (bC * ⟨k, hKC hk⟩)⁻¹ * (⟨k, hKC hk⟩ * bC) ∈ GLAPPrimeCore p ↥C :=
      QuotientGroup.eq.1 h1
    have hconj : (bC * ⟨k, hKC hk⟩) *
        ((bC * ⟨k, hKC hk⟩)⁻¹ * (⟨k, hKC hk⟩ * bC)) *
          (bC * ⟨k, hKC hk⟩)⁻¹ ∈ GLAPPrimeCore p ↥C :=
      (GLAPPrimeCore.normal p ↥C).conj_mem _ hu (bC * ⟨k, hKC hk⟩)
    have hEq : (bC * ⟨k, hKC hk⟩) *
        ((bC * ⟨k, hKC hk⟩)⁻¹ * (⟨k, hKC hk⟩ * bC)) *
          (bC * ⟨k, hKC hk⟩)⁻¹ = ⁅(⟨k, hKC hk⟩ : ↥C), bC⁆ := by
      rw [commutatorElement_def]
      group
    have hmemC' : ((⁅(⟨k, hKC hk⟩ : ↥C), bC⁆ : ↥C) : G) ∈ GLAPPrimeCoreOf p C := by
      rw [← hEq]
      exact (CFSG.HardMathSupport.Solomon.LocalBalance.mem_glaPPrimeCoreOf_iff
        (C := C) ((bC * ⟨k, hKC hk⟩) *
          ((bC * ⟨k, hKC hk⟩)⁻¹ * (⟨k, hKC hk⟩ * bC)) *
            (bC * ⟨k, hKC hk⟩)⁻¹)).2 hconj
    have hEqG : ((⁅(⟨k, hKC hk⟩ : ↥C), bC⁆ : ↥C) : G) = ⁅k, (bC : G)⁆ := rfl
    rw [hEqG] at hmemC'
    have hbkb : (bC : G) * k * (bC : G)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 hbK k).1 hk
    have hmemK : ⁅k, (bC : G)⁆ ∈ K := by
      have hEq2 : ⁅k, (bC : G)⁆ = k * ((bC : G) * k * (bC : G)⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [hEq2]
      exact K.mul_mem hk (K.inv_mem hbkb)
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
    exact ⟨hmemK, hmemC'⟩

theorem innDiagOn_map_subgroupOf {p : ℕ} (hp : p.Prime) {H L A : Subgroup G} (hLH : L ≤ H)
    {Ω : Type} [Group Ω] [Finite Ω] {π : ↥H →* Ω} (hN : ¬ p ∣ Nat.card π.ker)
    (h : InnDiagOn p A L) :
    InnDiagOn p ((A.subgroupOf H).map π) ((L.subgroupOf H).map π) := by
  have hAY : ∀ z ∈ A.subgroupOf H,
      z ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := fun z hz =>
    mem_normalizer_subgroupOf' z.2 (h.1 (Subgroup.mem_subgroupOf.1 hz))
  refine CFSG.LocalAnalysis.GLTheoremA.T156.innDiagOn_to_Omega
    (CFSG.LocalAnalysis.GLTheoremA.T156.compIso hp
      (Subgroup.map_subgroupOf_eq_of_le hLH) π hN) ?_ ?_ h
  · rintro _ ⟨z, hz, rfl⟩
    exact CFSG.LocalAnalysis.GLTheoremA.T156.map_normalizer_mem π (hAY z hz)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(z : G), Subgroup.mem_subgroupOf.1 hz, fun q q' =>
      CFSG.LocalAnalysis.GLTheoremA.T156.compIso_rel hp
        (Subgroup.map_subgroupOf_eq_of_le hLH) π hN (hAY z hz) q q'⟩


theorem card_eq_card_mul_inf_centModSubgroup {p : ℕ} (hp : p.Prime)
    {C K B : Subgroup G} {A W : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)}
    (hK : GLAPComponent p C K) (hBC : B ≤ C)
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set G))
    (hW : W = barX p C B ⊓ Subgroup.centralizer
      (barX p C K : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
    (hAB : A ≤ barX p C B) (hAW : A ⊓ W = ⊥) (hAsup : A ⊔ W = barX p C B) :
    Nat.card ↥B = Nat.card ↥A * Nat.card ↥(B ⊓ centModSubgroup p K) := by
  have hBp : IsPGroup p B :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isPGroup_of_isElemAbelian' hB
  have hBcard : Nat.card ↥B = Nat.card ↥(barX p C B) :=
    (card_barX_of_isPGroup hp hBp hBC).symm
  have hWB : W ≤ barX p C B := by
    rw [hW]
    exact inf_le_left
  have hW_eq : W = barX p C (B ⊓ centModSubgroup p K) := by
    rw [hW]
    exact (barX_inf_centModSubgroup hp hK.1 hK.2.1 hBN).symm
  have hWcard : Nat.card ↥W = Nat.card ↥(B ⊓ centModSubgroup p K) := by
    rw [hW_eq]
    exact card_barX_of_isPGroup hp (hBp.to_le inf_le_left) (inf_le_left.trans hBC)
  have hBelem : IsElemAbelian p (barX p C B) := isElemAbelian_barX hB
  have hprod : Nat.card ↥(barX p C B) = Nat.card ↥A * Nat.card ↥W := by
    rw [← hAsup]
    exact CFSG.card_sup_eq_mul_of_commute A W
      (fun a ha w hw => isElemAbelian_commute hBelem (hAB ha) (hWB hw)) hAW
  rw [hBcard, hprod, hWcard]

end CFSG.LocalAnalysis.GLTheoremA.T158

end
