module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (inner centerQuotient_conj)

section PCore

variable {G : Type*} [Group G] [Finite G]

theorem pPrimeCore_coprime_card_any (p : ℕ) (Y : Type*) [Group Y] [Finite Y] :
    Nat.Coprime p (Nat.card (CFSG.pPrimeCore p Y)) := by
  refine Nat.coprime_of_dvd fun q hq hqp hqn => ?_
  haveI : Fact q.Prime := ⟨hq⟩
  have hle : CFSG.pPrimeCore p Y ≤ CFSG.pPrimeCore q Y :=
    sSup_le_sSup fun K hK => ⟨hK.1, Nat.Coprime.coprime_dvd_left hqp hK.2⟩
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 CFSG.pPrimeCore_coprime_card
    (hqn.trans (Subgroup.card_dvd_of_le hle))

theorem coprime_card_pPrimeCoreOf (p : ℕ) (X : Subgroup G) :
    Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p X)) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact pPrimeCore_coprime_card_any p _

theorem pPrimeCoreOf_le_of_normal_any {p : ℕ} {H M : Subgroup G} (hHM : H ≤ M)
    (hn : (H.subgroupOf M).Normal) : GLAPPrimeCoreOf p H ≤ GLAPPrimeCoreOf p M := by
  have hMH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hn
  set O := GLAPPrimeCoreOf p H with hO
  have hOM : M ≤ Subgroup.normalizer (O : Set G) := by
    intro m hm
    have h1 := hMH hm
    rw [mem_normalizer_iff_gLBConj_eq] at h1 ⊢
    rw [hO, ← glaPPrimeCoreOf_gLBConj, h1]
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hOn : (O.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hOH.trans hHM)).2 hOM
  have hcop : Nat.Coprime p (Nat.card (O.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOH.trans hHM)).toEquiv]
    exact coprime_card_pPrimeCoreOf p H
  have hle : O.subgroupOf M ≤ GLAPPrimeCore p ↥M := le_sSup ⟨hOn, hcop⟩
  calc O = (O.subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (hOH.trans hHM)).symm
    _ ≤ GLAPPrimeCoreOf p M := Subgroup.map_mono hle

theorem pPrimeCoreOf_le_of_isSubnormal_any {p : ℕ} {L C : Subgroup G}
    (h : IsSubnormal L C) : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p C := by
  induction h with
  | refl => exact le_rfl
  | step hHM hn _ ih => exact (pPrimeCoreOf_le_of_normal_any hHM hn).trans ih

theorem ker_barMap_eq_any {p : ℕ} {C L : Subgroup G} (hLC : L ≤ C)
    (hsn : IsSubnormal L C) : (barMap p hLC).ker = GLAPPrimeCore p ↥L := by
  ext l
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (Subgroup.inclusion hLC l) = 1 :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    set K : Subgroup ↥L := (GLAPPrimeCoreOf p C).subgroupOf L with hK
    have hnorm : K.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_glaPPrimeCoreOf p C (hLC g.2)) (n : G)).1 ((Subgroup.mem_subgroupOf).1 hn)
      exact (Subgroup.mem_subgroupOf).2 (by simpa using h2)
    have hcop : Nat.Coprime p (Nat.card K) := by
      refine Nat.Coprime.coprime_dvd_right ?_ (coprime_card_pPrimeCoreOf p C)
      have hc : Nat.card (K.map L.subtype) = Nat.card K :=
        Subgroup.card_map_of_injective L.subtype_injective
      rw [← hc]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hk
    have hKle : K ≤ GLAPPrimeCore p ↥L := le_sSup ⟨hnorm, hcop⟩
    exact hKle ((Subgroup.mem_subgroupOf).2 ⟨_, h1, rfl⟩)
  · intro hl
    have h1 : (l : G) ∈ GLAPPrimeCoreOf p L := ⟨l, hl, rfl⟩
    obtain ⟨c, hc, hcl⟩ := pPrimeCoreOf_le_of_isSubnormal_any hsn h1
    have hcl' : Subgroup.inclusion hLC l = c := Subtype.ext hcl.symm
    refine Subtype.ext ?_
    change QuotientGroup.mk' (GLAPPrimeCore p ↥C) (Subgroup.inclusion hLC l) = 1
    rw [hcl', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hc

end PCore

section Quasisimple

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_pQuot_any {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) :
    CFSG.Open.IsQuasisimple (PQuot p L) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (ker_barMap_eq_any hL.1 hL.2.1).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (barMap p hL.1)
        (barMap_surjective hL.1))).symm hL.2.2.1.2.2

theorem pQuot_one_subsingleton (L : Subgroup G) : Subsingleton (PQuot 1 L) := by
  have h : GLAPPrimeCore 1 ↥L = ⊤ :=
    top_le_iff.1 (le_sSup ⟨inferInstance, Nat.coprime_one_left _⟩)
  change Subsingleton (↥L ⧸ GLAPPrimeCore 1 ↥L)
  rw [h]
  exact QuotientGroup.subsingleton_quotient_top

theorem not_glaPComponent_one {X L : Subgroup G} : ¬ GLAPComponent 1 X L := fun hL => by
  haveI := pQuot_one_subsingleton L
  haveI := isQuasisimple_nontrivial (isQuasisimple_pQuot_any hL)
  exact not_subsingleton _ ‹_›

theorem indAut_mem_inner_iff_any {p : ℕ} {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot p L)) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    indAut p L g hg ∈ inner (PSimple p L) ↔ InducesInnerMod p L g := by
  haveI : Group.IsPerfect (PQuot p L) := ⟨hq.1⟩
  have key : chevAut p L ⟨g, hg⟩ ∈ inner (PSimple p L) ↔ InducesInnerMod p L g := by
    rw [inducesInnerMod_iff_barAut_mem_inner hg]
    constructor
    · intro h
      exact mem_inner_of_centerQuotientHom_mem h
    · rintro ⟨k, hk⟩
      refine ⟨QuotientGroup.mk' (Subgroup.center (PQuot p L)) k, ?_⟩
      rw [← centerQuotient_conj, hk]
      rfl
  rw [← key]
  have : indAut p L g hg = (chevAut p L ⟨g, hg⟩)⁻¹ := by
    rw [indAut, ← map_inv]
    rfl
  rw [this]
  exact inv_mem_iff

end Quasisimple

end MI

end CFSG.LocalAnalysis.GLTheoremA
