module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53JrC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53JrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53T1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y53_A_le_S (s : Setting3 G L) : s.fr.A ≤ s.fr.S := by
  show Subgroup.closure {s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂} ≤
    Subgroup.closure {s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀}
  exact Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

private theorem y53_zSeries_le (n : ℕ) (T : Subgroup G) : zSeries n T ≤ T := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

private theorem y53_exists_maxElemAbelian_ge {Γ : Type} [Group Γ] [Finite Γ]
    {E : Subgroup Γ} (hE : IsElemAbelian 2 E) :
    ∃ M : Subgroup Γ, M ∈ maxElemAbelian (⊤ : Subgroup Γ) ∧ E ≤ M := by
  haveI : Finite (Subgroup Γ) :=
    Finite.of_injective (fun H : Subgroup Γ => (H : Set Γ)) SetLike.coe_injective
  let T : Set (Subgroup Γ) := {M | E ≤ M ∧ IsElemAbelian 2 M}
  have hTfin : T.Finite := Set.toFinite T
  have hTne : T.Nonempty := ⟨E, le_rfl, hE⟩
  obtain ⟨M, hMT, hMmax⟩ :=
    Set.exists_max_image T (fun M : Subgroup Γ => Nat.card M) hTfin hTne
  refine ⟨M, ⟨le_top, hMT.2, ?_⟩, hMT.1⟩
  intro M' hMM' _ hM'e
  exact (Subgroup.eq_of_le_of_card_ge hMM' (hMmax M' ⟨hMT.1.trans hMM', hM'e⟩)).symm

private theorem y53_thompsonRank_top_eq_of_maxElemAbelian_pair {Γ : Type} [Group Γ] [Finite Γ]
    {Ab D : Subgroup Γ} (hmax : maxElemAbelian (⊤ : Subgroup Γ) = {Ab, D})
    (hcardAb : Nat.card Ab = 16) (hcardD : Nat.card D ≤ 8)
    (hcent : ∀ x : Γ, (∀ a ∈ Ab, x * a = a * x) → x ∈ Ab) :
    thompsonRank (⊤ : Subgroup Γ) = Ab := by
  have hAbmem : Ab ∈ maxElemAbelian (⊤ : Subgroup Γ) := hmax.symm ▸ (by simp)
  have hAbe : IsElemAbelian 2 Ab := hAbmem.2.1
  have hMsplit : ∀ M : Subgroup Γ, M ∈ maxElemAbelian (⊤ : Subgroup Γ) → M = Ab ∨ M = D := by
    intro M hM
    have h : M ∈ ({Ab, D} : Set (Subgroup Γ)) := hmax ▸ hM
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hbound : ∀ E : Subgroup Γ, IsElemAbelian 2 E → Nat.card E ≤ 16 := by
    intro E hE
    obtain ⟨M, hMmem, hEM⟩ := y53_exists_maxElemAbelian_ge hE
    rcases hMsplit M hMmem with rfl | rfl
    · exact (Subgroup.card_le_of_le hEM).trans (le_of_eq hcardAb)
    · exact (Subgroup.card_le_of_le hEM).trans (hcardD.trans (by norm_num))
  have hcard16 : ∀ E : Subgroup Γ, IsElemAbelian 2 E → Nat.card E = 16 → E = Ab := by
    intro E hE hEcard
    obtain ⟨M, hMmem, hEM⟩ := y53_exists_maxElemAbelian_ge hE
    rcases hMsplit M hMmem with hMA | hMD
    · rw [hMA] at hEM
      exact Subgroup.eq_of_le_of_card_ge hEM (by rw [hcardAb, hEcard])
    · exfalso
      rw [hMD] at hEM
      have hle : Nat.card E ≤ Nat.card D := Subgroup.card_le_of_le hEM
      omega
  have hOpenRank_le : ∀ U : Subgroup Γ, CFSG.Open.pRank 2 U ≤ 4 := by
    intro U
    refine CFSG.SectionRank.pRank_le one_lt_two (fun E _ hE => ?_)
    calc Nat.card E ≤ 16 := hbound E hE
      _ = 2 ^ 4 := by norm_num
  have hAbOpenRank : CFSG.Open.pRank 2 Ab = 4 := by
    refine le_antisymm (hOpenRank_le Ab) ?_
    exact CFSG.SectionRank.le_pRank one_lt_two le_rfl hAbe (by rw [hcardAb]; norm_num)
  have hRank_le : ∀ U : Subgroup Γ, CFSG.pRank 2 U ≤ 4 := by
    intro U
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hOpenRank_le U
  have hAbRank : CFSG.pRank 2 Ab = 4 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hAbOpenRank
  apply le_antisymm
  · rw [thompsonRank]
    refine iSup_le fun U => iSup_le fun hU => iSup_le fun hcomm => iSup_le fun hmaxU => ?_
    have hrankU : CFSG.pRank 2 U = 4 := by
      refine le_antisymm (hRank_le U) ?_
      calc (4 : ℕ) = CFSG.pRank 2 Ab := hAbRank.symm
        _ ≤ CFSG.pRank 2 U := hmaxU Ab le_top hAbe.1
    have hErank : CFSG.Open.pRank 2 (⊤ : Subgroup ↥U) = 4 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hrankU
    obtain ⟨E₀, -, hE₀e, hE₀c⟩ := CFSG.SectionRank.exists_pRank one_lt_two (⊤ : Subgroup ↥U)
    have hE₀c' : Nat.card E₀ = 16 := by rw [hE₀c, hErank]; norm_num
    have hEe : IsElemAbelian 2 (E₀.map U.subtype) :=
      CFSG.SectionRank.isElemAbelian_map hE₀e U.subtype
    have hEc : Nat.card (E₀.map U.subtype) = 16 := by
      rw [Subgroup.card_map_of_injective U.subtype_injective, hE₀c']
    have hEeq : E₀.map U.subtype = Ab := hcard16 _ hEe hEc
    have hAbU : Ab ≤ U := hEeq ▸ Subgroup.map_subtype_le E₀
    intro x hx
    refine hcent x (fun a ha => ?_)
    haveI : IsMulCommutative U := hcomm
    simpa using mul_comm' (⟨x, hx⟩ : U) (⟨a, hAbU ha⟩ : U)
  · rw [thompsonRank]
    refine le_iSup_of_le Ab (le_iSup_of_le le_top (le_iSup_of_le hAbe.1 (le_iSup_of_le ?_ le_rfl)))
    intro V _ hV
    calc CFSG.pRank 2 V ≤ 4 := hRank_le V
      _ = CFSG.pRank 2 Ab := hAbRank.symm

theorem y53_jrS {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    SecProp s.fr.S s.fr.Z (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) = (s.fr.A.subgroupOf s.fr.S).map π) := by
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  obtain ⟨hZnorm, hmax⟩ := hH.hLF.fact14.2.2.2.2.1.2.1
  refine ⟨hZnorm, ?_⟩
  let N : Subgroup ↥s.fr.S := s.fr.Z.subgroupOf s.fr.S
  haveI hNnorm : N.Normal := hZnorm
  let Ab : Subgroup (↥s.fr.S ⧸ N) := (s.fr.A.subgroupOf s.fr.S).map (QuotientGroup.mk' N)
  let D : Subgroup (↥s.fr.S ⧸ N) :=
    ((zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}).subgroupOf s.fr.S).map (QuotientGroup.mk' N)
  have hZleA : s.fr.Z ≤ s.fr.A := by
    show Subgroup.zpowers s.fr.z ≤ s.fr.A
    exact Subgroup.zpowers_le.mpr hA.z_mem
  have hZleS : s.fr.Z ≤ s.fr.S := hZleA.trans (y53_A_le_S s)
  have hNleA : N ≤ s.fr.A.subgroupOf s.fr.S := Subgroup.subgroupOf_mono s.fr.S hZleA
  have hNcard : Nat.card N = 2 := by
    show Nat.card (s.fr.Z.subgroupOf s.fr.S) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleS).toEquiv,
      show Nat.card s.fr.Z = 2 from by
        rw [show s.fr.Z = Subgroup.zpowers s.fr.z from rfl, Nat.card_zpowers, hA.z_order]]
  have hAcard : Nat.card (s.fr.A.subgroupOf s.fr.S) = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y53_A_le_S s)).toEquiv, hA.card_A]
  have hAbcard : Nat.card Ab = 16 := by
    have hmk := QuotientGroup.card_preimage_mk N (Ab : Set (↥s.fr.S ⧸ N))
    have hcomap : Subgroup.comap (QuotientGroup.mk' N) Ab = N ⊔ s.fr.A.subgroupOf s.fr.S := by
      show Subgroup.comap (QuotientGroup.mk' N)
        ((s.fr.A.subgroupOf s.fr.S).map (QuotientGroup.mk' N)) = N ⊔ s.fr.A.subgroupOf s.fr.S
      rw [QuotientGroup.comap_map_mk']
    have hsup : N ⊔ s.fr.A.subgroupOf s.fr.S = s.fr.A.subgroupOf s.fr.S :=
      sup_eq_right.mpr hNleA
    have hmk' : Nat.card (Subgroup.comap (QuotientGroup.mk' N) Ab) =
        Nat.card N * Nat.card Ab := hmk
    rw [hcomap, hsup, hAcard, hNcard] at hmk'
    omega
  have hzSeries : zSeries 2 s.fr.S = Subgroup.closure {s.fr.b₁, s.fr.b₂} :=
    hH.hLF.fact14.1.2.1.trans hH.hLF.fact14.1.2.2.1
  have hz_closure : s.fr.z ∈ Subgroup.closure {s.fr.b₁, s.fr.b₂} := by
    show s.fr.b₁ ^ 2 ∈ Subgroup.closure {s.fr.b₁, s.fr.b₂}
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  have hZleD : s.fr.Z ≤ zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀} := by
    show Subgroup.zpowers s.fr.z ≤ _
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left ?_)
    rw [hzSeries]
    exact hz_closure
  have hDleS : zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀} ≤ s.fr.S := by
    refine sup_le (y53_zSeries_le 2 s.fr.S) ?_
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.subset_closure (by simp)
  have hD16frame : Nat.card ↥(zSeries 2 (frameWith s 1).S ⊔
      Subgroup.closure {(frameWith s 1).h₀}) = 16 := by
    obtain ⟨eD⟩ := hH.hLF.fact14.2.2.2.2.1.2.2
    rw [Nat.card_congr eD.toEquiv, Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
      DihedralGroup.card]
  have hD16 : Nat.card ↥(zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}) = 16 := hD16frame
  have hNleD : N ≤ (zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}).subgroupOf s.fr.S :=
    Subgroup.subgroupOf_mono s.fr.S hZleD
  have hDcard : Nat.card D ≤ 8 := by
    have hmk := QuotientGroup.card_preimage_mk N (D : Set (↥s.fr.S ⧸ N))
    have hcomap : Subgroup.comap (QuotientGroup.mk' N) D =
        N ⊔ (zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}).subgroupOf s.fr.S := by
      show Subgroup.comap (QuotientGroup.mk' N)
        (((zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}).subgroupOf s.fr.S).map
          (QuotientGroup.mk' N)) = _
      rw [QuotientGroup.comap_map_mk']
    have hsup : N ⊔ (zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}).subgroupOf s.fr.S =
        (zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}).subgroupOf s.fr.S :=
      sup_eq_right.mpr hNleD
    have hDsub : Nat.card
        ((zSeries 2 s.fr.S ⊔ Subgroup.closure {s.fr.h₀}).subgroupOf s.fr.S) = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleS).toEquiv, hD16]
    have hmk' : Nat.card (Subgroup.comap (QuotientGroup.mk' N) D) =
        Nat.card N * Nat.card D := hmk
    rw [hcomap, hsup, hDsub, hNcard] at hmk'
    omega
  have hcent : ∀ x : ↥s.fr.S ⧸ N, (∀ a ∈ Ab, x * a = a * x) → x ∈ Ab := by
    intro x hx
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hwA : (w : G) ∈ s.fr.A := by
      refine y53_centS hH (w : G) w.2 ?_
      intro a ha
      have ha' : (QuotientGroup.mk' N) ⟨a, y53_A_le_S s ha⟩ ∈ Ab :=
        Subgroup.mem_map.mpr ⟨⟨a, y53_A_le_S s ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have hcomm := hx _ ha'
      have h1 : (QuotientGroup.mk' N) ⁅(⟨a, y53_A_le_S s ha⟩ : ↥s.fr.S), w⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
      have hmem : ⁅(⟨a, y53_A_le_S s ha⟩ : ↥s.fr.S), w⁆ ∈ N :=
        (QuotientGroup.eq_one_iff ⁅(⟨a, y53_A_le_S s ha⟩ : ↥s.fr.S), w⁆).mp h1
      rw [Subgroup.mem_subgroupOf] at hmem
      change s.fr.S.subtype ⁅(⟨a, y53_A_le_S s ha⟩ : ↥s.fr.S), w⁆ ∈ s.fr.Z at hmem
      rw [map_commutatorElement] at hmem
      simpa using hmem
    exact Subgroup.mem_map.mpr ⟨w, Subgroup.mem_subgroupOf.mpr hwA, rfl⟩
  have hmax' : maxElemAbelian (⊤ : Subgroup (↥s.fr.S ⧸ N)) = {Ab, D} := hmax
  exact y53_thompsonRank_top_eq_of_maxElemAbelian_pair hmax' hAbcard hDcard hcent

theorem y53_jrS_T1 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    SecProp c.e.T₁ c.s.fr.Z (fun Y _ _ π =>
      thompsonRank ((c.s.fr.S.subgroupOf c.e.T₁).map π) =
        (c.s.fr.A.subgroupOf c.e.T₁).map π) := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have hWT : c.s.fr.S ≤ c.e.T₁ := hH.h32.2.1.1
  have hZW : c.s.fr.Z ≤ c.s.fr.S :=
    (show Subgroup.zpowers c.s.fr.z ≤ c.s.fr.A from Subgroup.zpowers_le.mpr hA.z_mem).trans
      (y53_A_le_S c.s)
  have hAW : c.s.fr.A ≤ c.s.fr.S := y53_A_le_S c.s
  exact y53_section_transport hWT hZW hAW (y5_Z_normal_T1 hH) (y53_jrS hH)

end CFSG.OddStandard.HigherRank.YamadaG23
