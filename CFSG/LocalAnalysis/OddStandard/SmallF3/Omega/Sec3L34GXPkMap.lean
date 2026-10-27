module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTFix

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_x_orderOf_map {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {a : A} (ha : orderOf a = 2) : orderOf (ρ a) = 2 := by
  have ha2 : a * a = 1 := by
    rw [← pow_two]
    exact ha ▸ pow_orderOf_eq_one a
  have hne : ρ a ≠ 1 := by
    intro h1
    have h1' : a = 1 := h.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) ha2
    rw [h1', orderOf_one] at ha
    exact absurd ha (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ hne
  rw [pow_two, ← map_mul, ha2, map_one]

theorem l34g_x_sl23PocketIn_subgroupOf {H V K : Subgroup G} {y : G} (hVH : V ≤ H) (hyH : y ∈ H)
    (h : Sl23PocketIn V y K) :
    Sl23PocketIn (V.subgroupOf H) (⟨y, hyH⟩ : ↥H) (K.subgroupOf H) := by
  obtain ⟨hyK, hKle, hKsub, hKmod⟩ := h
  have hKH : K ≤ H := hKle.trans (inf_le_left.trans hVH)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact hyK
  · refine le_inf ?_ ?_
    · intro k hk
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact (hKle hk).1
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [Subgroup.mem_subgroupOf] at hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKle hk).2
  ·
    let C : Subgroup G := V ⊓ centralizer ({y} : Set G)
    let C' : Subgroup ↥H := V.subgroupOf H ⊓ centralizer ({⟨y, hyH⟩} : Set ↥H)
    let ψ : ↥C' →* G := H.subtype.comp C'.subtype
    have hmem : ∀ x : ↥C', ψ x ∈ C := by
      intro x
      obtain ⟨hxV, hxZ⟩ := Subgroup.mem_inf.mp x.2
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxV, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hxZ)
    let f : ↥C' →* ↥C := ψ.codRestrict C hmem
    have hcomap : (K.subgroupOf C).comap f = (K.subgroupOf H).subgroupOf C' := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rfl
    change ((K.subgroupOf H).subgroupOf C').IsSubnormal
    rw [← hcomap]
    exact hKsub.comap f
  · exact isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hKmod

theorem l34g_x_isI4PlusIn_subgroupOf {H V : Subgroup G} {y : G} (hVH : V ≤ H) (hyH : y ∈ H)
    (h : IsI4PlusIn V y) : IsI4PlusIn (V.subgroupOf H) (⟨y, hyH⟩ : ↥H) := by
  obtain ⟨hy2, K, hK⟩ := h
  exact ⟨(Subgroup.orderOf_mk y hyH).trans hy2,
    K.subgroupOf H, l34g_x_sl23PocketIn_subgroupOf hVH hyH hK⟩

theorem l34g_x_isSubnormal_map {A P : Type} [Group A] [Group P] (ρ : A →* P) {C K : Subgroup A}
    (hKC : K ≤ C) (hK : (K.subgroupOf C).IsSubnormal) :
    ((K.map ρ).subgroupOf (C.map ρ)).IsSubnormal := by
  let f : ↥C →* ↥(C.map ρ) := ρ.subgroupMap C
  have hmap : (K.subgroupOf C).map f = (K.map ρ).subgroupOf (C.map ρ) := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨x, hxC⟩, hxK, hxy⟩
      exact ⟨x, hxK, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hxK, hxy⟩
      exact ⟨⟨x, hKC hxK⟩, hxK, Subtype.ext hxy⟩
  rw [← hmap]
  exact Subgroup.IsSubnormal.map (MonoidHom.subgroupMap_surjective ρ C) hK

theorem l34g_x_isSL23Mod_map {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ρ : A →* P} (h : OddCentralCover ρ) {K : Subgroup A} (hK : IsSL23Mod ↥K) :
    IsSL23Mod ↥(K.map ρ) := by
  let φ : ↥K →* ↥(K.map ρ) := ρ.subgroupMap K
  have hφ : Function.Surjective φ := MonoidHom.subgroupMap_surjective ρ K
  have hker : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map K.subtype ≤ ρ.ker := by
      rintro _ ⟨k, hk, rfl⟩
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))
    have hcard : Nat.card φ.ker = Nat.card (φ.ker.map K.subtype) :=
      Nat.card_congr (φ.ker.equivMapOfInjective K.subtype K.subtype_injective).toEquiv
    rw [hcard]
    exact h.odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  obtain ⟨e⟩ := hK
  exact ⟨(sec63PT_oddCoreQuotientEquiv φ hφ hker).symm.trans e⟩

theorem l34g_x_sl23PocketIn_map {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ρ : A →* P} (h : OddCentralCover ρ) {V K : Subgroup A} {b : A} (hb : b * b = 1)
    (hK : Sl23PocketIn V b K) : Sl23PocketIn (V.map ρ) (ρ b) (K.map ρ) := by
  obtain ⟨hbK, hKle, hKsub, hKmod⟩ := hK
  refine ⟨Subgroup.mem_map_of_mem ρ hbK, ?_, ?_, ?_⟩
  · rw [← sec63PT_map_inf_centralizer h hb]
    exact Subgroup.map_mono hKle
  · rw [← sec63PT_map_inf_centralizer h hb]
    exact l34g_x_isSubnormal_map ρ hKle hKsub
  · exact l34g_x_isSL23Mod_map h hKmod

theorem l34g_x_isI4PlusIn_map {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ρ : A →* P} (h : OddCentralCover ρ) {V : Subgroup A} {b : A} (hb : IsI4PlusIn V b) :
    IsI4PlusIn (V.map ρ) (ρ b) := by
  obtain ⟨hb2, K, hK⟩ := hb
  have hb1 : b * b = 1 := by
    rw [← pow_two]
    exact hb2 ▸ pow_orderOf_eq_one b
  exact ⟨l34g_x_orderOf_map h hb2, K.map ρ, l34g_x_sl23PocketIn_map h hb1 hK⟩

end CFSG.OddStandard.SmallF3.Omega
