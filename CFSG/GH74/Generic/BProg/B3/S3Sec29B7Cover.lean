module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29BLayer

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement MatrixGroups

namespace S3Sec29B7Cover

variable {G : Type} [Group G] [Finite G]

theorem cover_of_mem_cSec {I : Subgroup G} {t : G} (ht : t ∈ cSec I) (ht2 : orderOf t = 2)
    (i : ↥I) :
    ∃ i' : ↥I, (i' : G) * t = t * (i' : G) ∧ i⁻¹ * i' ∈ pPrimeCore 2 ↥I := by
  obtain ⟨htN, htO, htc⟩ := ht
  set H : Subgroup G := normalizer (I : Set G) with hH
  have hOI : pPrimeCoreOf 2 I ≤ I := TwoThin.pPrimeCoreOf_le I
  have hIH : I ≤ H := Subgroup.le_normalizer
  have hHN : H ≤ normalizer (pPrimeCoreOf 2 I : Set G) := fun q hq =>
    TwoThin.mem_normalizer_pPrimeCoreOf hq
  set N : Subgroup ↥H := (pPrimeCoreOf 2 I).subgroupOf H with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (hOI.trans hIH)).2 hHN
  have hNodd : Odd (Nat.card N) := by
    rw [hN, S3Sec29BLayer.card_subgroupOf_of_le (hOI.trans hIH)]
    exact TwoThin.card_pPrimeCoreOf_odd I
  set iH : ↥H := ⟨(i : G), hIH i.2⟩ with hiH
  set tH : ↥H := ⟨t, htN⟩ with htHdef
  have htH2 : orderOf tH = 2 := by
    rw [htHdef, Subgroup.orderOf_mk]
    exact ht2
  have hcomm : QuotientGroup.mk' N tH * QuotientGroup.mk' N iH =
      QuotientGroup.mk' N iH * QuotientGroup.mk' N tH := by
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine Subgroup.mem_subgroupOf.2 ?_
    have h1 := htc (i : G) i.2
    have h2 : ⁅t, (i : G)⁆ = (⁅(i : G), t⁆)⁻¹ := (commutatorElement_inv _ _).symm
    show ⁅t, (i : G)⁆ ∈ pPrimeCoreOf 2 I
    rw [h2]
    exact inv_mem h1
  have hc' : ∀ a ∈ zpowers tH, QuotientGroup.mk' N a * QuotientGroup.mk' N iH =
      QuotientGroup.mk' N iH * QuotientGroup.mk' N a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [map_zpow]
    exact (Commute.zpow_left (show Commute (QuotientGroup.mk' N tH) (QuotientGroup.mk' N iH)
      from hcomm) n).eq
  obtain ⟨g', hg'1, hg'2⟩ := B1.centralizer_quotient_of_pGroup N hNodd
    (B1.isPGroup_two_zpowers_of_orderOf htH2) (c := QuotientGroup.mk' N iH) hc'
  have hg't : (g' : G) * t = t * (g' : G) :=
    (congrArg Subtype.val (hg'2 tH (Subgroup.mem_zpowers tH))).symm
  have hzO : (g' : G)⁻¹ * (i : G) ∈ pPrimeCoreOf 2 I := by
    have h1 : g'⁻¹ * iH ∈ N := QuotientGroup.eq.1 hg'1
    exact Subgroup.mem_subgroupOf.1 h1
  have hg'I : (g' : G) ∈ I := by
    have : (g' : G) = (i : G) * ((g' : G)⁻¹ * (i : G))⁻¹ := by group
    rw [this]
    exact I.mul_mem i.2 (I.inv_mem (hOI hzO))
  refine ⟨⟨(g' : G), hg'I⟩, hg't, ?_⟩
  have h3 : (i : G)⁻¹ * (g' : G) ∈ pPrimeCoreOf 2 I := by
    have := (pPrimeCoreOf 2 I).inv_mem hzO
    rwa [mul_inv_rev, inv_inv] at this
  obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.1 h3
  have : o = i⁻¹ * ⟨(g' : G), hg'I⟩ := Subtype.ext hoeq
  rw [← this]
  exact ho

omit [Finite G] in
theorem not_isSolvable_of_sl2 {X : Type} [Group X]
    (h : HasSL2Model X (fun q => Odd q ∧ 5 ≤ q)) : ¬ Group.IsSolvable X := by
  obtain ⟨F, hF, hFin, ⟨hodd, h5⟩, ⟨e⟩⟩ := h
  have hq : IsQuasisimple SL(2, F) := CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by omega)
  have hX : IsQuasisimple X := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((specialLinearGroupEquivStatedSL 2 F).trans e.symm) hq
  have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hX
  have : Group.IsPerfect X := hX.1
  exact Group.IsPerfect.not_isSolvable X

end S3Sec29B7Cover

end CFSG.GH74.Generic.BProg.B3
