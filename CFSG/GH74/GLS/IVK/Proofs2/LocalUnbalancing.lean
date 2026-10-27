module

public import CFSG.GH74.GLS.C3.Layer1.Defs

import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk103
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4

lemma exists_locally_unbalancing_of_quotient_odd_core
    {G : Type} [Group G] [Finite G]
    {x : G} {K : Subgroup G}
    (hpair : IsIL2Pair x K)
    (hcenter : Subgroup.center (K ⧸ pPrimeCore 2 K) = ⊥)
    (hex : ∃ ub : K ⧸ pPrimeCore 2 K,
      orderOf ub = 2 ∧
      pPrimeCoreOf 2
        (Subgroup.centralizer ({ub} : Set (K ⧸ pPrimeCore 2 K))) ≠ ⊥) :
    ∃ y ∈ K, IsLocallyUnbalancing x y K := by
  obtain ⟨ub, hub, hxu⟩ := hex
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  obtain ⟨u, hu2, rfl⟩ := exists_lift_involution (pPrimeCore 2 ↥K) hNodd hub
  obtain ⟨k0, hk0, hk0ne⟩ :=
    exists_mem_pPrimeCoreOf_centralizer (pPrimeCore 2 ↥K) hNodd hu2 hxu
  set y : G := (u : G) with hy
  have hyK : y ∈ K := u.2
  have hy2 : orderOf y = 2 := by rw [hy, Subgroup.orderOf_coe]; exact hu2
  have hKX : K ≤ centralizer ({x} : Set G) := hpair.2.1
  have hyX : y ∈ centralizer ({x} : Set G) := hKX hyK
  refine ⟨y, hyK, hpair, hy2, hyX, le_normalizer hyK, ?_⟩
  intro hle
  set Z : Subgroup G := centralizer ({x, y} : Set G) with hZdef
  have hZmem : ∀ z, z ∈ Z ↔ z * x = x * z ∧ z * y = y * z := by
    intro z
    simp only [hZdef, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
  have hZX : Z ≤ centralizer ({x} : Set G) := fun z hz => by
    rw [mem_centralizer_singleton_iff]
    exact ((hZmem z).1 hz).1
  have hZN : Z ≤ normalizer (K : Set G) := by
    intro z hz
    by_contra hzN
    have hzX : z ∈ centralizer ({x} : Set G) := hZX hz
    have hK' : cmap z K ≠ K := fun h =>
      hzN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    have hcX' : cmap z (centralizer ({x} : Set G)) = centralizer ({x} : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer hzX)
    have hK'c : IsPCompIn 2 (centralizer ({x} : Set G)) (cmap z K) := by
      have := isPCompIn_cmap hpair.2 z
      rwa [hcX'] at this
    have h1 : cmap z K ≤ cSec K := le_cSec_of_ne hK'c hpair.2 hK'
    have hyK' : y ∈ cmap z K := by
      rw [mem_cmap]
      have e : z⁻¹ * y * z = y := by
        have := ((hZmem z).1 hz).2
        rw [mul_assoc, ← this]
        group
      rw [e]
      exact hyK
    have hcen' := mk_mem_center_of_mem_centralizerSection (a := u) (h1 hyK')
    rw [hcenter, Subgroup.mem_bot] at hcen'
    rw [hcen', orderOf_one] at hub
    omega
  set D : Subgroup G := K ⊓ centralizer ({y} : Set G) with hDdef
  have hDK : D ≤ K := inf_le_left
  have hDZ : D ≤ Z := fun d hd => by
    rw [hZmem]
    exact ⟨mem_centralizer_singleton_iff.1 (hKX hd.1), mem_centralizer_singleton_iff.1 hd.2⟩
  have hZY : ∀ z ∈ Z, z ∈ centralizer ({y} : Set G) := fun z hz => by
    rw [mem_centralizer_singleton_iff]
    exact ((hZmem z).1 hz).2
  have hDnorm : ∀ z ∈ Z, z ∈ normalizer (D : Set G) := fun z hz =>
    TwoThin.mem_normalizer_inf (hZN hz) (le_normalizer (hZY z hz))
  have hWD : pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 Z := by
    refine le_pPrimeCoreOf_of_normalized' ((TwoThin.pPrimeCoreOf_le D).trans hDZ) ?_
      (TwoThin.card_pPrimeCoreOf_odd D)
    intro c hc w hw
    exact TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer (hDnorm c hc) hw
  have hDsub : D.subgroupOf K = Subgroup.centralizer ({u} : Set ↥K) := by
    ext a
    constructor
    · intro h
      rw [Subgroup.mem_subgroupOf] at h
      exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 h.2))
    · intro h
      rw [Subgroup.mem_subgroupOf]
      exact ⟨a.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 h))⟩
  have hkD : (k0 : G) ∈ pPrimeCoreOf 2 D := by
    rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hDK, hDsub]
    exact ⟨k0, hk0, rfl⟩
  have hkc : (k0 : G) ∈ centralizerSection K (pPrimeCoreOf 2 K) := hle (hWD hkD)
  have hk1 := mk_mem_center_of_mem_centralizerSection (a := k0) hkc
  rw [hcenter, Subgroup.mem_bot] at hk1
  exact hk0ne hk1

lemma exists_locally_unbalancing_of_a7
    {G : Type} [Group G] [Finite G]
    {x : G} {K : Subgroup G}
    (hpair : IsIL2Pair x K)
    (hA7 : Nonempty ((K ⧸ pPrimeCore 2 K) ≃* alternatingGroup (Fin 7))) :
    ∃ y ∈ K, IsLocallyUnbalancing x y K := by
  have hq : IsQuasisimple (K ⧸ pPrimeCore 2 K) := TwoThin.isQuasisimple_hat hpair.2
  have hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K) := by
    obtain ⟨e⟩ := hA7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hcenter : Subgroup.center (K ⧸ pPrimeCore 2 K) = ⊥ :=
    center_eq_bot_of_simple_quasisimple hs hq
  obtain ⟨ub, hub⟩ := exists_prime_orderOf_dvd_card'
    (G := K ⧸ pPrimeCore 2 K) 2 (even_card_of_simple_quasisimple hs hq)
  have hne : pPrimeCoreOf 2
      (Subgroup.centralizer ({ub} : Set (K ⧸ pPrimeCore 2 K))) ≠ ⊥ := by
    intro hbot
    apply (ivk_1_18.2 (K ⧸ pPrimeCore 2 K) hA7 ub hub).1
    unfold xu
    rw [Lemma118.fixedSubgroup_conj]
    exact hbot
  exact exists_locally_unbalancing_of_quotient_odd_core hpair hcenter ⟨ub, hub, hne⟩

end CFSG.GH74.GLS
