module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5AbsQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

theorem f7_card_center {t : G} (ht : orderOf t = 2) (h : centerIn L = zpowers t) :
    Nat.card ↥(Subgroup.center ↥L) = 2 := by
  have h1 : Nat.card ↥(centerIn L) = Nat.card ↥(Subgroup.center ↥L) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective L)
  rw [← h1, h, Nat.card_zpowers, ht]

theorem f7_center_mem {t : G} {B : Subgroup G} (h : centerIn L = zpowers t) (htB : t ∈ B)
    {k : ↥L} (hk : k ∈ Subgroup.center ↥L) : (k : G) ∈ B := by
  have h1 : (k : G) ∈ centerIn L := Subgroup.mem_map_of_mem L.subtype hk
  rw [h] at h1
  exact (Subgroup.zpowers_le.mpr htB) h1

theorem f7_center_sq (hc : Nat.card ↥(Subgroup.center ↥L) = 2) {k : ↥L}
    (hk : k ∈ Subgroup.center ↥L) : k * k = 1 := by
  have h1 : orderOf k ∣ 2 := hc ▸ Subgroup.orderOf_dvd_natCard _ hk
  have h2 : k ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  rwa [pow_two] at h2

theorem f7_ffImg_isElemAb2 {H : Type} [Group H] {φ : ↥L →* H} {B : Subgroup G} {k : ℕ}
    (hBL : B ≤ L) (hB : IsElemAb2 B (k + 1)) (hker : φ.ker ≤ B.subgroupOf L)
    (hcard : Nat.card ↥φ.ker = 2) : IsElemAb2 (ffImg φ B) k := by
  unfold IsElemAb2 CFSG.Open.IsElemAbelian
  obtain ⟨⟨hcomm, hpow⟩, hcardB⟩ := hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsMulCommutative ↥B := hcomm
    exact Subgroup.map_isMulCommutative (H := B.subgroupOf L) φ
  · intro y hy
    obtain ⟨l, hl, rfl⟩ := mem_ffImg_iff.mp hy
    have hl2 : l ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hpow (l : G) hl
    rw [← map_pow, hl2, map_one]
  · have h := Subgroup.relIndex_mul_card (H := φ.ker) (K := B.subgroupOf L)
    rw [Subgroup.relIndex_ker (f := φ), inf_eq_left.mpr hker, hcard] at h
    have hBc : Nat.card ↥(B.subgroupOf L) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
    have h' : Nat.card ↥(ffImg φ B) * 2 = 2 ^ k * 2 := by
      change Nat.card ↥((B.subgroupOf L).map φ) * 2 = _
      rw [h, hBc, hcardB, pow_succ]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem f7_lift_mem {H : Type} [Group H] {φ : ↥L →* H} {B : Subgroup G}
    (hker : φ.ker ≤ B.subgroupOf L) {b k : ↥L} (hb : (b : G) ∈ B) (h : φ k = φ b) :
    (k : G) ∈ B := by
  have h1 : b⁻¹ * k ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h2 : (((b⁻¹ * k : ↥L)) : G) ∈ B := Subgroup.mem_subgroupOf.mp (hker h1)
  have h3 : (k : G) = (b : G) * (((b⁻¹ * k : ↥L)) : G) := by
    simp
  rw [h3]
  exact B.mul_mem hb h2

private theorem f7_map_subtype_cent (s : ↥L) :
    ((⊤ : Subgroup ↥L) ⊓ centralizer ({s} : Set ↥L)).map L.subtype =
      L ⊓ centralizer ({(s : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨-, hc⟩ := Subgroup.mem_inf.mp hl
    refine Subgroup.mem_inf.mpr ⟨l.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact congrArg Subtype.val hc
  · intro hg
    obtain ⟨hgL, hgc⟩ := Subgroup.mem_inf.mp hg
    refine ⟨⟨g, hgL⟩, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
    exact Subtype.ext hgc

theorem f7_exists_lift {M : Type} [Group M] (F : ↥L →* M) (hz : F.ker ≤ Subgroup.center ↥L)
    (h2 : ∀ k ∈ F.ker, k * k = 1) (s : ↥L) {x : M}
    (hx : x ∈ twoRes ((⊤ : Subgroup ↥L).map F ⊓ centralizer ({F s} : Set M))) :
    ∃ k : ↥L, F k = x ∧ (k : G) ∈ twoRes (L ⊓ centralizer ({(s : G)} : Set G)) := by
  rw [map_twoRes_cent F hz h2 ⊤ s] at hx
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  refine ⟨k, rfl, ?_⟩
  have hker : ∀ g ∈ L.subtype.ker, g * g = 1 := by
    intro g hg
    rw [Subgroup.ker_subtype, Subgroup.mem_bot] at hg
    rw [hg, one_mul]
  have hmem : (k : G) ∈
      (twoRes ((⊤ : Subgroup ↥L) ⊓ centralizer ({s} : Set ↥L))).map L.subtype :=
    Subgroup.mem_map_of_mem L.subtype hk
  rw [map_twoRes L.subtype hker, f7_map_subtype_cent] at hmem
  exact hmem

end CFSG.OddStandard.SmallF3.Omega
