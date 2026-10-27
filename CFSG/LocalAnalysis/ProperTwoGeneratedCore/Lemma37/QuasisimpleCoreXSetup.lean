module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreBad
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreFourGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreQuasi

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.BenderSuzuki.PFAppendixIII

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

structure EscapingLift (B : Subgroup J) (z u : J) : Prop where
  mem : u ∈ B
  sq : u * u = centralElt J
  commute : Commute (u : J ⧸ Subgroup.center J) (z : J ⧸ Subgroup.center J)
  escape : ¬ Subgroup.centralizer ({(u : J ⧸ Subgroup.center J)} : Set (J ⧸ Subgroup.center J))
    ≤ B.map (QuotientGroup.mk' (Subgroup.center J))

structure BadLift (B : Subgroup J) (z u : J) : Prop extends EscapingLift B z u where
  not_embedded : ¬ fusionStronglyEmbedded
    ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J)))

theorem Setting.exists_badLift
    (h : Setting J Q B) : ∃ z, FourGen Q z ∧ ∃ u, BadLift B z u := by
  obtain ⟨z, hz, u, huB, hu, huz, hesc, hnot⟩ := h.exists_bad_lift
  exact ⟨z, hz, u, ⟨⟨huB, hu, huz, hesc⟩, hnot⟩⟩

abbrev quasiNormalizer (u : J) : Subgroup J :=
  Subgroup.normalizer (Subgroup.zpowers u : Set J)

abbrev QuasiQuotient (u : J) :=
  quasiNormalizer u ⧸ pPrimeCore 2 (quasiNormalizer u)

abbrev quasiMk (u : J) : quasiNormalizer u →* QuasiQuotient u :=
  QuotientGroup.mk' _

abbrev quasiSelf (u : J) : quasiNormalizer u :=
  ⟨u, Subgroup.le_normalizer (Subgroup.mem_zpowers u)⟩

abbrev quasiBar (u : J) : QuasiQuotient u :=
  quasiMk u (quasiSelf u)

abbrev quasiCentral (u : J) : QuasiQuotient u :=
  quasiBar u * quasiBar u

abbrev quasiImage (B : Subgroup J) (u : J) : Subgroup (QuasiQuotient u) :=
  (B.subgroupOf (quasiNormalizer u)).map (quasiMk u)

omit [Finite J] in
theorem zpowers_quasiSelf_normal (u : J) : (Subgroup.zpowers (quasiSelf u)).Normal := by
  have heq : Subgroup.zpowers (quasiSelf u) =
      (Subgroup.zpowers u).subgroupOf (quasiNormalizer u) := by
    have hmap : (Subgroup.zpowers (quasiSelf u)).map (quasiNormalizer u).subtype =
        Subgroup.zpowers u :=
      MonoidHom.map_zpowers _ _
    rw [Subgroup.subgroupOf, ← hmap,
      Subgroup.comap_map_eq_self_of_injective (quasiNormalizer u).subtype_injective]
  rw [heq]
  exact Subgroup.normal_in_normalizer

theorem Setting.centralElt_mem_quasiNormalizer (h : Setting J Q B) (u : J) :
    centralElt J ∈ quasiNormalizer u := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  rw [← (h.commute_centralElt n).eq, mul_inv_cancel_right]

theorem Setting.orderOf_centralElt_mk (h : Setting J Q B) (u : J) :
    orderOf (⟨centralElt J, h.centralElt_mem_quasiNormalizer u⟩ : quasiNormalizer u) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact h.orderOf_centralElt

theorem Setting.centralElt_mk_mem_center (h : Setting J Q B) (u : J) :
    (⟨centralElt J, h.centralElt_mem_quasiNormalizer u⟩ : quasiNormalizer u) ∈
      Subgroup.center (quasiNormalizer u) :=
  Subgroup.mem_center_iff.mpr fun x => Subtype.ext (h.commute_centralElt x).eq

namespace EscapingLift

theorem centralElt_mk_eq (hu : EscapingLift B z u) (h : Setting J Q B) :
    (⟨centralElt J, h.centralElt_mem_quasiNormalizer u⟩ : quasiNormalizer u) =
      quasiSelf u * quasiSelf u :=
  Subtype.ext hu.sq.symm

theorem mem_quasiNormalizer_iff (hu : EscapingLift B z u) (h : Setting J Q B) {x : J} :
    x ∈ quasiNormalizer u ↔
      Commute (x : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J) :=
  h.mem_normalizer_zpowers_iff_commute hu.sq

theorem mem_quasiNormalizer (hu : EscapingLift B z u) (h : Setting J Q B) :
    z ∈ quasiNormalizer u :=
  (hu.mem_quasiNormalizer_iff h).mpr hu.commute.symm

theorem not_le (hu : EscapingLift B z u) (h : Setting J Q B) : ¬ quasiNormalizer u ≤ B := by
  intro hle
  apply hu.escape
  intro g hg
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [h.mk_mem_map_iff]
  exact hle ((hu.mem_quasiNormalizer_iff h).mpr (Subgroup.mem_centralizer_singleton_iff.mp hg))

theorem subgroupOf_ne_top (hu : EscapingLift B z u) (h : Setting J Q B) :
    B.subgroupOf (quasiNormalizer u) ≠ ⊤ := by
  intro htop
  apply hu.not_le h
  intro x hx
  have hmem : (⟨x, hx⟩ : quasiNormalizer u) ∈ B.subgroupOf (quasiNormalizer u) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem two_le_pRank (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z) :
    2 ≤ CFSG.Open.pRank 2 (B ⊓ quasiNormalizer u) :=
  two_le_pRank_of_commuting_involutions ⟨h.centralElt_mem, h.centralElt_mem_quasiNormalizer u⟩
    ⟨hz.mem_of_setting h, hu.mem_quasiNormalizer h⟩ h.orderOf_centralElt hz.order
    (hz.ne_centralElt h).symm (h.commute_centralElt z).symm

end EscapingLift

theorem Setting.gamma_le (h : Setting J Q B) (M : Subgroup J) (T : Sylow 2 M)
    (hT : (T : Subgroup M) ≤ B.subgroupOf M) :
    properTwoGenCoreGamma (T : Subgroup M) 2 ≤ B.subgroupOf M :=
  centralizer_full_core_le_overgroup Q B h.sylow_le h.core_le M T
    (Subgroup.map_le_iff_le_comap.mpr hT)

theorem Setting.sylow_le_of_le (h : Setting J Q B) (M : Subgroup J) (T : Sylow 2 M)
    {D : Subgroup J} (hDT : D ≤ (T : Subgroup M).map M.subtype) (hDB : D ≤ B)
    (hD : 2 ≤ CFSG.Open.pRank 2 D) : (T : Subgroup M) ≤ B.subgroupOf M := by
  have hle : (T : Subgroup M).map M.subtype ≤ B :=
    pGroup_le_of_large_intersection Q B 2 h.sylow_le h.core_le _ (T.isPGroup'.map M.subtype)
      (hD.trans (CFSG.SectionRank.pRank_mono (by decide) (le_inf hDT hDB)))
  exact fun x hx => Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem _ hx))

theorem EscapingLift.exists_sylow (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) :
    ∃ T : Sylow 2 (quasiNormalizer u),
      (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u) ∧
      quasiSelf u ∈ (T : Subgroup (quasiNormalizer u)) ∧
      (⟨z, hu.mem_quasiNormalizer h⟩ : quasiNormalizer u) ∈ (T : Subgroup (quasiNormalizer u)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := zpowers_quasiSelf_normal u
  have hu2 : IsPGroup 2 (Subgroup.zpowers (quasiSelf u)) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_eq_four hu.sq]
    norm_num)
  have hz2 : IsPGroup 2 (Subgroup.zpowers (⟨z, hu.mem_quasiNormalizer h⟩ : quasiNormalizer u)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz.order, pow_one])
  obtain ⟨T, hDT⟩ := (hu2.to_sup_of_normal_left hz2).exists_le_sylow
  have huT : quasiSelf u ∈ (T : Subgroup (quasiNormalizer u)) :=
    hDT (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have hzT : (⟨z, hu.mem_quasiNormalizer h⟩ : quasiNormalizer u) ∈
      (T : Subgroup (quasiNormalizer u)) :=
    hDT (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine ⟨T, h.sylow_le_of_le _ T (D := fourGroup z) (fourGroup_le ?_ ⟨_, hzT, rfl⟩)
    (hz.fourGroup_le_core h) (hz.two_le_pRank_fourGroup h), huT, hzT⟩
  rw [← hu.sq]
  exact ⟨quasiSelf u * quasiSelf u, (T : Subgroup (quasiNormalizer u)).mul_mem huT huT, rfl⟩

namespace EscapingLift

theorem hull_not_le (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z) :
    ¬ localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J) ≤
      B.map (QuotientGroup.mk' (Subgroup.center J)) := by
  intro hle
  apply hu.escape
  intro g hg
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [h.mk_mem_map_iff]
  have hxu : Commute (x : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J) :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hcls : ((x * z * x⁻¹ : J) : J ⧸ Subgroup.center J) ∈
      involutionPointClass (z : J ⧸ Subgroup.center J) :=
    ⟨(x : J ⧸ Subgroup.center J)⁻¹, by
      simp only [rightConjugateElem, inv_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩
  have hcomm : Commute ((x * z * x⁻¹ : J) : J ⧸ Subgroup.center J)
      (u : J ⧸ Subgroup.center J) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact (hxu.mul_left hu.commute.symm).mul_left hxu.inv_left
  have hmem := hle (mem_localInvolutionPointHull hcls hcomm)
  rw [h.mk_mem_map_iff] at hmem
  exact h.mem_of_conj_mem (hz.mem_of_setting h) hz.order hz.not_mem_center hmem

end EscapingLift

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
