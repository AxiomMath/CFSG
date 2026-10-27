module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Two

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit
open scoped MatrixGroups

private theorem not_isPerfect_sl2_zmod3 : ¬ Group.IsPerfect SL(2, ZMod 3) := by
  intro hP
  have : (CFSG.ClassicalInvolution.sl2ThreeQ).Normal := CFSG.ClassicalInvolution.sl2ThreeQ_normal
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (SL(2, ZMod 3) ⧸ CFSG.ClassicalInvolution.sl2ThreeQ) :=
    isCyclic_of_prime_card (p := 3)
      (by rw [← Subgroup.index_eq_card]; exact CFSG.ClassicalInvolution.sl2ThreeQ_index)
  have hle := (Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := CFSG.ClassicalInvolution.sl2ThreeQ)).mp inferInstance
  rw [hP.commutator_eq_top, top_le_iff] at hle
  have h3 := CFSG.ClassicalInvolution.sl2ThreeQ_index
  rw [hle, Subgroup.index_top] at h3
  omega

theorem isTwoQuasisimple_of_classBMember {L : Type} [Group L] {J : Subgroup L} {u : L}
    (hJ : IsClassBMember L J u) : IsTwoQuasisimple ↥J := by
  rcases hJ.mtype with ⟨hq, -⟩ | ⟨-, ⟨e⟩⟩
  · exact hq
  · exfalso
    haveI : Group.IsPerfect ↥J := hJ.perfect
    haveI : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
        (QuotientGroup.mk'_surjective _)
    exact not_isPerfect_sl2_zmod3 (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem exists_fourGroup_of_classBMember
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} (ht2 : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    {J : Subgroup ↥L} {u : ↥L} (hJ : IsClassBMember ↥L J u) :
    ∃ W : Subgroup G, (∀ a ∈ W, a * a = 1) ∧ Nat.card ↥W = 4 ∧ t ∈ W ∧ (u : G) ∈ W ∧
      t ∉ zpowers (u : G) ∧ (u : G) ≠ 1 ∧ (u : G) ∈ J.map L.subtype ∧
      IsTwoComponentIn (J.map L.subtype) (centralizer (W : Set G)) ∧
      IsMTypeSchur 3 ↥(J.map L.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu'2 : orderOf ((u : ↥L) : G) = 2 := by
    rw [Subgroup.orderOf_coe, hJ.orderOf_eq_two]
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht2; exact absurd ht2 (by norm_num)
  have hu'1 : (u : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu'2; exact absurd hu'2 (by norm_num)
  have htu_ne : t ≠ (u : G) := by
    intro h
    apply hJ.not_mem_center
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hx := Subgroup.mem_centralizer_singleton_iff.mp (hLt x.2)
    rw [h] at hx
    simpa using hx
  have hc : t * (u : G) = (u : G) * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hLt u.2)).symm
  set W : Subgroup G := Subgroup.closure ({t, (u : G)} : Set G) with hWdef
  obtain ⟨hW2', hW4'⟩ :=
    Lemma47.fourGroup_closure_pair (β := t) (z := (u : G)) ht2 hu'2 htu_ne.symm hc
  have hW2 : ∀ a ∈ W, a * a = 1 := by rw [hWdef]; exact hW2'
  have hW4 : Nat.card ↥W = 4 := by rw [hWdef]; exact hW4'
  have htW : t ∈ W := by
    rw [hWdef]; exact Subgroup.subset_closure (by simp)
  have hu'W : (u : G) ∈ W := by
    rw [hWdef]; exact Subgroup.subset_closure (by simp)
  have htu : t ∉ zpowers (u : G) := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers_two hu'2 hmem with h | h
    · exact ht1 h
    · exact htu_ne h
  have hCW : centralizer (W : Set G) =
      centralizer ({t} : Set G) ⊓ centralizer ({(u : G)} : Set G) := by
    rw [hWdef]
    exact Lemma47.centralizer_closure_pair t (u : G)
  have hCWleC : centralizer (W : Set G) ≤ centralizer ({t} : Set G) := by
    rw [hCW]; exact inf_le_left
  have hLeq : L ⊓ centralizer (W : Set G) =
      L ⊓ centralizer ({(u : G)} : Set G) := by
    rw [hCW, ← inf_assoc, inf_eq_left.mpr hLt]
  have eJ : ↥J ≃* ↥(J.map L.subtype) :=
    Subgroup.equivMapOfInjective J L.subtype L.subtype_injective
  have hqJ' : IsTwoQuasisimple ↥(J.map L.subtype) :=
    isTwoQuasisimple_of_mulEquiv eJ (isTwoQuasisimple_of_classBMember hJ)
  have hJ'leL : J.map L.subtype ≤ L := Subgroup.map_subtype_le J
  have hJ'leCW : J.map L.subtype ≤ centralizer (W : Set G) := by
    rw [hCW]
    refine le_inf (hJ'leL.trans hLt) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hx with ⟨y, hyJ, rfl⟩
    have hy : y ∈ centralizer ({u} : Set ↥L) := CFSG.Open.IsSubnormal.le hJ.subnormal hyJ
    simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  have hmapC : (centralizer ({u} : Set ↥L)).map L.subtype =
      L ⊓ centralizer ({(u : G)} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr (by
        simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
    · rintro ⟨hxL, hx⟩
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp hx))
  have hsub_map : CFSG.Open.IsSubnormal (J.map L.subtype)
      ((centralizer ({u} : Set ↥L)).map L.subtype) :=
    CFSG.Open.IsSubnormal.map L.subtype hJ.subnormal
  have hsub_map' : CFSG.Open.IsSubnormal (J.map L.subtype)
      (L ⊓ centralizer ({(u : G)} : Set G)) := by
    rwa [hmapC] at hsub_map
  have hLsub : CFSG.Open.IsSubnormal L (centralizer ({t} : Set G)) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hLt).mpr
      ((isTwoComponent_iff_isPComponent
        (L.subgroupOf (centralizer ({t} : Set G)))).mpr hLp).1
  have hsub_inf : CFSG.Open.IsSubnormal (L ⊓ centralizer (W : Set G))
      (centralizer (W : Set G)) :=
    CFSG.Open.IsSubnormal.inf_of_le hLsub hCWleC
  have hsub_all : CFSG.Open.IsSubnormal (J.map L.subtype) (centralizer (W : Set G)) := by
    have h1 : CFSG.Open.IsSubnormal (J.map L.subtype) (L ⊓ centralizer (W : Set G)) := by
      rw [hLeq]; exact hsub_map'
    exact CFSG.Open.IsSubnormal.trans h1 hsub_inf
  have hJ'sub : ((J.map L.subtype).subgroupOf (centralizer (W : Set G))).IsSubnormal :=
    CFSG.Open.IsSubnormal.subgroupOf hsub_all
  exact ⟨W, hW2, hW4, htW, hu'W, htu, hu'1, Subgroup.mem_map.mpr ⟨u, hJ.mem, rfl⟩,
    ⟨hJ'leCW, hJ'sub, hqJ'⟩, T23.isMTypeSchur_of_mulEquiv eJ hJ.mtype⟩

end CFSG.OddStandard.HigherRank.F3
