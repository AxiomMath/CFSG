module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Tools

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG CFSG.ComponentClassification.HarrisLit CFSG.ClassicalInvolution.Generic

theorem exists_fourGroup_of_classicalMember
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} (ht2 : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    {J : Subgroup ↥L} {u : ↥L} (hJ : IsClassicalMember p f J u) (hu : u ∉ center ↥L) :
    ∃ W : Subgroup G, (∀ a ∈ W, a * a = 1) ∧ Nat.card ↥W = 4 ∧ t ∈ W ∧ (u : G) ∈ W ∧
      t ∉ zpowers (u : G) ∧ (u : G) ≠ 1 ∧ (u : G) ∈ J.map L.subtype ∧
      IsTwoComponentIn (J.map L.subtype) (centralizer (W : Set G)) ∧
      IsMTypeSchur p ↥(J.map L.subtype) ∧
      IsSLTwoOver (p ^ f) (↥(J.map L.subtype) ⧸ pPrimeCore 2 ↥(J.map L.subtype)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu'2 : orderOf ((u : ↥L) : G) = 2 := by
    rw [Subgroup.orderOf_coe, hJ.orderOf_eq_two]
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht2; exact absurd ht2 (by norm_num)
  have hu'1 : (u : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu'2; exact absurd hu'2 (by norm_num)
  have htu_ne : t ≠ (u : G) := by
    intro h
    apply hu
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
  obtain ⟨eSL⟩ := hJ.nonempty_equiv
  have hcore : CFSG.Open.classicalInvolutionOddCore ↥J = pPrimeCore 2 ↥J :=
    CFSG.ComponentClassification.TBLit.classicalInvolutionOddCore_eq ↥J
  have eO : (↥J ⧸ CFSG.Open.classicalInvolutionOddCore ↥J) ≃*
      (↥J ⧸ pPrimeCore 2 ↥J) :=
    QuotientGroup.quotientMulEquivOfEq hcore
  have eQ : (↥J ⧸ pPrimeCore 2 ↥J) ≃*
      (↥(J.map L.subtype) ⧸ pPrimeCore 2 ↥(J.map L.subtype)) :=
    QuotientGroup.congr _ _ eJ (CFSG.pPrimeCore_map_iso 2 eJ)
  letI hFintype : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p f) = p ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p f (by omega)
  have hsl' : IsSLTwoOver (p ^ f)
      (↥(J.map L.subtype) ⧸ pPrimeCore 2 ↥(J.map L.subtype)) :=
    ⟨GaloisField p f, inferInstance, hFintype, hcard,
      ⟨eQ.symm.trans (eO.symm.trans eSL)⟩⟩
  have hperfJ' : Group.IsPerfect ↥(J.map L.subtype) := by
    haveI : Group.IsPerfect ↥J := hJ.perfect
    exact Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hqJ' : IsTwoQuasisimple ↥(J.map L.subtype) :=
    ⟨hperfJ', (Lemma47.sl2_facts (Fact.out : p.Prime) hp2 hf h5 hsl').1⟩
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
  have hM : IsMTypeSchur p ↥(J.map L.subtype) :=
    T23.isMTypeSchur_of_slTwo hGA hperfJ' (Fact.out : p.Prime) hp2 hf h5 hsl'
  exact ⟨W, hW2, hW4, htW, hu'W, htu, hu'1, Subgroup.mem_map.mpr ⟨u, hJ.mem, rfl⟩,
    ⟨hJ'leCW, hJ'sub, hqJ'⟩, hM, hsl'⟩

end CFSG.OddStandard.HigherRank
