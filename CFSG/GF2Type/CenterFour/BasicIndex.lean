module

public import CFSG.GF2Type.CenterFour.Basic

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

theorem Config.commutator_mul (hC : Config z n) {t q q' : G} (ht : t ∈ coreAt z)
    (hq : q ∈ coreAt z) (hq' : q' ∈ coreAt z) : ⁅t, q * q'⁆ = ⁅t, q⁆ * ⁅t, q'⁆ := by
  have hqz : q * z = z * q := Subgroup.mem_centralizer_singleton_iff.mp (hC.core_le_centralizer hq)
  have hgrp : ⁅t, q * q'⁆ = ⁅t, q⁆ * (q * ⁅t, q'⁆ * q⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hcentral : q * ⁅t, q'⁆ * q⁻¹ = ⁅t, q'⁆ := by
    rcases hC.comm_eq t ht q' hq' with h | h
    · simp [h]
    · rw [h, mul_inv_eq_iff_eq_mul]
      exact hqz
  rw [hgrp, hcentral]

private def commHomIdx (hC : Config z n) {t : G} (ht : t ∈ coreAt z) : ↥(coreAt z) →* G :=
  MonoidHom.mk' (fun q => ⁅t, (q : G)⁆) (fun a b => hC.commutator_mul ht a.2 b.2)

private lemma commHomIdx_apply (hC : Config z n) {t : G} (ht : t ∈ coreAt z) (q : ↥(coreAt z)) :
    commHomIdx hC ht q = ⁅t, (q : G)⁆ := rfl

private lemma exists_commutator_ne_one_of_nmem_center (hC : Config z n) {t : G}
    (ht : t ∈ coreAt z) (htZ : t ∉ centerAt z) : ∃ q ∈ coreAt z, ⁅t, q⁆ ≠ 1 := by
  by_contra hne
  push_neg at hne
  apply htZ
  unfold centerAt
  refine Subgroup.mem_map.mpr ⟨⟨t, ht⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  rintro ⟨g, hg⟩
  have h1 : t * g = g * t := commutatorElement_eq_one_iff_mul_comm.mp (hne g hg)
  exact Subtype.ext h1.symm

private lemma range_commHomIdx (hC : Config z n) {t : G} (ht : t ∈ coreAt z)
    (htZ : t ∉ centerAt z) : (commHomIdx hC ht).range = zpowers z := by
  apply le_antisymm
  · intro x hx
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [commHomIdx_apply]
    rcases hC.comm_eq t ht (q : G) q.2 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]
    obtain ⟨q, hq, hne⟩ := exists_commutator_ne_one_of_nmem_center hC ht htZ
    have hz : ⁅t, q⁆ = z := (hC.comm_eq t ht q hq).resolve_left hne
    exact MonoidHom.mem_range.mpr ⟨⟨q, hq⟩, by rw [commHomIdx_apply]; exact hz⟩

private lemma ker_commHomIdx (hC : Config z n) {t : G} (ht : t ∈ coreAt z) :
    (commHomIdx hC ht).ker = (coreAt z ⊓ centralizer ({t} : Set G)).subgroupOf (coreAt z) := by
  ext q
  rw [MonoidHom.mem_ker, commHomIdx_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro h
    exact ⟨q.2, h.symm⟩
  · rintro ⟨_, h⟩
    exact h.symm

theorem Config.card_centralizer_mul_two (hC : Config z n) {t : G} (ht : t ∈ coreAt z)
    (htZ : t ∉ centerAt z) :
    Nat.card (coreAt z ⊓ centralizer ({t} : Set G) : Subgroup G) * 2 = Nat.card (coreAt z) := by
  have hidx : (commHomIdx hC ht).ker.index = 2 := by
    rw [Subgroup.index_ker, range_commHomIdx hC ht htZ, Nat.card_zpowers, hC.orderOf_eq]
  have hcardker : Nat.card (commHomIdx hC ht).ker =
      Nat.card (coreAt z ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    rw [ker_commHomIdx hC ht]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_mul_index (commHomIdx hC ht).ker
  rw [hidx, hcardker] at hmul
  exact hmul

end CFSG.GF2Type.CenterFour
