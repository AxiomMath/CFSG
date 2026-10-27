module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTgrp

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup

theorem factorization_two_card_le_of_le_centralizer {X : Type*} [Group X] [Finite X]
    {E : Subgroup X} [E.Normal] {u : X} {T : Subgroup X} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hTu : T ≤ centralizer ({u} : Set X)) :
    (Nat.card E).factorization 2 ≤
      (Nat.card ↥(E ⊓ centralizer ({u} : Set X))).factorization 2 := by
  let C : Subgroup X := centralizer ({u} : Set X)
  have hXne : Nat.card X ≠ 0 := (Nat.card_pos (α := X)).ne'
  have hcardXT : Nat.card ↥T * T.index = Nat.card X := Subgroup.card_mul_index T
  have hcardXE : Nat.card ↥E * E.index = Nat.card X := Subgroup.card_mul_index E
  have hTne : Nat.card ↥T ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hcardXT
    exact hXne hcardXT.symm
  have htind_ne : T.index ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hcardXT
    exact hXne hcardXT.symm
  have hEne : Nat.card ↥E ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hcardXE
    exact hXne hcardXE.symm
  have hcardT : Nat.card ↥(E.subgroupOf T) * E.relIndex T = Nat.card ↥T :=
    Subgroup.card_mul_index (E.subgroupOf T)
  have hr : E.relIndex T ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hcardT
    exact hTne hcardT.symm
  have hNEne : Nat.card ↥(E.subgroupOf T) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hcardT
    exact hTne hcardT.symm
  obtain ⟨s, hs⟩ := Subgroup.relIndex_dvd_index_of_normal (H := E) (K := T)
  have hkey : Nat.card ↥(E.subgroupOf T) * T.index = Nat.card ↥E * s :=
    mul_right_cancel₀ hr (by
      calc (Nat.card ↥(E.subgroupOf T) * T.index) * E.relIndex T
          = (Nat.card ↥(E.subgroupOf T) * E.relIndex T) * T.index := by ring
        _ = Nat.card ↥T * T.index := by rw [hcardT]
        _ = Nat.card X := hcardXT
        _ = Nat.card ↥E * E.index := hcardXE.symm
        _ = Nat.card ↥E * (E.relIndex T * s) := by rw [hs]
        _ = (Nat.card ↥E * s) * E.relIndex T := by ring)
  have hs_ne : s ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hkey
    exact (mul_ne_zero hNEne htind_ne) hkey
  have hfac := congrArg (fun n : ℕ => n.factorization 2) hkey
  rw [Nat.factorization_mul hNEne htind_ne, Nat.factorization_mul hEne hs_ne] at hfac
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hTidx, add_zero] at hfac
  have hvle : (Nat.card ↥E).factorization 2 ≤
      (Nat.card (E.subgroupOf T)).factorization 2 := by
    rw [hfac]
    omega
  have hdiv : 2 ^ (Nat.card ↥E).factorization 2 ∣ Nat.card (E.subgroupOf T) :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hNEne).mpr hvle
  have hcard_eq : Nat.card (E.subgroupOf T) = Nat.card ↥(E ⊓ T) := by
    rw [← Subgroup.subgroupOf_map_subtype E T,
      Subgroup.card_map_of_injective (f := T.subtype) Subtype.coe_injective]
  have hdiv' : 2 ^ (Nat.card ↥E).factorization 2 ∣ Nat.card ↥(E ⊓ T) := by
    rw [hcard_eq] at hdiv
    exact hdiv
  have hET_le : E ⊓ T ≤ E ⊓ C := le_inf inf_le_left (inf_le_right.trans hTu)
  have hdvd : Nat.card ↥(E ⊓ T) ∣ Nat.card ↥(E ⊓ C) := Subgroup.card_dvd_of_le hET_le
  have hCne : Nat.card ↥(E ⊓ C) ≠ 0 := by
    intro h0
    have h := Subgroup.card_mul_index (E ⊓ C)
    rw [h0, zero_mul] at h
    exact hXne h.symm
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hCne).mp (hdiv'.trans hdvd)

theorem not_two_dvd_index_map_of_surjective {C X : Type*} [Group C] [Group X] [Finite C]
    (ψ : C →* X) (hψ : Function.Surjective ψ) {P : Subgroup C} (hP : ¬ 2 ∣ P.index) :
    ¬ 2 ∣ (P.map ψ).index := by
  intro h
  exact hP (h.trans (P.index_map_dvd hψ))

theorem not_two_dvd_index_of_normalizer_le_centralizer {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} {x : G} (hT : IsPGroup 2 T) (hTx : T ≤ centralizer ({x} : Set G))
    (hodd : ¬ 2 ∣ (T.subgroupOf (centralizer ({x} : Set G))).index)
    (hnorm : ∀ g ∈ normalizer (T : Set G), g * x * g⁻¹ = x) : ¬ 2 ∣ T.index := by
  let C : Subgroup G := centralizer ({x} : Set G)
  intro hd
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  by_cases hTPeq : T = (P : Subgroup G)
  · rw [hTPeq] at hd
    exact P.not_dvd_index hd
  · have hTPlt : T < (P : Subgroup G) := lt_of_le_of_ne hTP hTPeq
    haveI : Group.IsNilpotent (↥(P : Subgroup G)) := P.isPGroup'.isNilpotent
    have hNC : NormalizerCondition (↥(P : Subgroup G)) :=
      Group.normalizerCondition_of_isNilpotent
    have hproper : T.subgroupOf (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      exact hTPeq (le_antisymm hTP (Subgroup.subgroupOf_eq_top.mp h))
    obtain ⟨y, hyN, hyT⟩ :=
      SetLike.exists_of_lt (hNC (T.subgroupOf (P : Subgroup G)) hproper)
    have hyN' : (y : G) ∈ normalizer (T : Set G) := by
      have hEq := Subgroup.subgroupOf_normalizer_eq hTP
      rw [← hEq] at hyN
      exact Subgroup.mem_subgroupOf.1 hyN
    have hynT : (y : G) ∉ T := fun h => hyT (Subgroup.mem_subgroupOf.2 h)
    let M : Subgroup G := (P : Subgroup G) ⊓ normalizer (T : Set G)
    have hTM : T ≤ M := fun t ht => ⟨hTP ht, Subgroup.le_normalizer ht⟩
    have hyM : (y : G) ∈ M := ⟨y.2, hyN'⟩
    have hTltM : T < M := by
      refine lt_of_le_of_ne hTM ?_
      intro hTM'
      rw [← hTM'] at hyM
      exact hynT hyM
    have hMC : M ≤ C := by
      intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m * x = (m * x * m⁻¹) * m := by group
        _ = x * m := by rw [hnorm m hm.2]
    have hM2 : IsPGroup 2 M := P.isPGroup'.to_le inf_le_left
    have hrel : (T.subgroupOf C).index = (T.subgroupOf M).index * (M.subgroupOf C).index := by
      have hle : T.subgroupOf C ≤ M.subgroupOf C := Subgroup.subgroupOf_mono C hTM
      have h1 := Subgroup.relIndex_mul_index (H := T.subgroupOf C) (K := M.subgroupOf C) hle
      have h2 := Subgroup.relIndex_subgroupOf (H := T) (K := M) (L := C) hMC
      have h3 : T.relIndex M = (T.subgroupOf M).index := rfl
      rw [h2, h3] at h1
      exact h1.symm
    obtain ⟨n, hn⟩ := hM2.index (T.subgroupOf M)
    have hne1 : (T.subgroupOf M).index ≠ 1 := by
      intro h1
      have htop : T.subgroupOf M = ⊤ := Subgroup.index_eq_one.mp h1
      exact (not_le_of_gt hTltM) (Subgroup.subgroupOf_eq_top.mp htop)
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      exact hne1 hn
    have hdvdM : 2 ∣ (T.subgroupOf M).index := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [hn, pow_succ]
      exact dvd_mul_left 2 _
    have hdvdC : 2 ∣ (T.subgroupOf C).index := by
      rw [hrel]
      exact dvd_mul_of_dvd_left hdvdM _
    exact hodd hdvdC

theorem forall_normalizer_conj_eq_of_fgrp {G : Type} [Group G] {T : Subgroup G} {x : G}
    (hxF : x ∈ Fgrp T) (hu : ∀ u ∈ Fgrp T, IsConj x u → u = x) :
    ∀ g ∈ normalizer (T : Set G), g * x * g⁻¹ = x := by
  intro g hg
  have hgF : g ∈ normalizer (Fgrp T : Set G) := normalizer_le_normalizer_Fgrp T hg
  have hmem : g * x * g⁻¹ ∈ Fgrp T := (Subgroup.mem_normalizer_iff.mp hgF x).mp hxF
  exact hu _ hmem (isConj_iff.mpr ⟨g, rfl⟩)

theorem exists_sylow_two_centralizer {G : Type*} [Group G] [Finite G] {x w : G} (hx2 : x * x = 1)
    (hw : w ∈ centralizer ({x} : Set G)) (hw2 : w * w = 1) :
    ∃ T : Subgroup G, T ≤ centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ (T.subgroupOf (centralizer ({x} : Set G))).index ∧ w ∈ T ∧ x ∈ T := by
  let C : Subgroup G := centralizer ({x} : Set G)
  have hxC_mem : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  let xC : ↥C := ⟨x, hxC_mem⟩
  let wC : ↥C := ⟨w, hw⟩
  have hwC2 : wC * wC = 1 := by
    apply Subtype.ext
    show w * w = (1 : G)
    exact hw2
  have hwCord : orderOf wC ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hwC2
  have hwP : IsPGroup 2 (zpowers wC) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      simpa using hwCord)
  have hxC2 : xC * xC = 1 := by
    apply Subtype.ext
    show x * x = (1 : G)
    exact hx2
  have hxCord : orderOf xC ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hxC2
  have hxP : IsPGroup 2 (zpowers xC) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      simpa using hxCord)
  have hxCcenter : xC ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp c.2
  haveI : (zpowers xC).Normal := Subgroup.normal_of_le_center (zpowers_le.2 hxCcenter)
  obtain ⟨P, hPw⟩ := hwP.exists_le_sylow
  have hZle : zpowers xC ≤ (P : Subgroup ↥C) := hxP.le_sylow_of_normal P
  have hxCP : xC ∈ (P : Subgroup ↥C) := hZle (Subgroup.mem_zpowers xC)
  have hwCP : wC ∈ (P : Subgroup ↥C) := hPw (Subgroup.mem_zpowers wC)
  refine ⟨(P : Subgroup ↥C).map C.subtype, Subgroup.map_subtype_le (P : Subgroup ↥C),
    P.isPGroup'.map C.subtype, ?_, ?_, ?_⟩
  · have hsub : ((P : Subgroup ↥C).map C.subtype).subgroupOf C = (P : Subgroup ↥C) := by
      ext c
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨p, hp, hpc⟩
        rw [← Subtype.coe_injective hpc]
        exact hp
      · intro hc
        exact ⟨c, hc, rfl⟩
    rw [hsub]
    exact P.not_dvd_index
  · exact Subgroup.mem_map.mpr ⟨wC, hwCP, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨xC, hxCP, rfl⟩

theorem not_two_dvd_index_of_fgrp_conj {G : Type} [Group G] [Finite G] {T : Subgroup G} {x : G}
    (hT : IsPGroup 2 T) (hTx : T ≤ centralizer ({x} : Set G))
    (hodd : ¬ 2 ∣ (T.subgroupOf (centralizer ({x} : Set G))).index) (hxT : x ∈ T)
    (hu : ∀ u ∈ Fgrp T, IsConj x u → u = x) : ¬ 2 ∣ T.index := by
  have hxF : x ∈ Fgrp T := by
    rw [Fgrp, Subgroup.mem_inf]
    refine ⟨?_, hxT⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTx ht)
  exact not_two_dvd_index_of_normalizer_le_centralizer hT hTx hodd
    (forall_normalizer_conj_eq_of_fgrp hxF hu)

end CFSG.OddStandard.AltStdSec.SwapPattern
