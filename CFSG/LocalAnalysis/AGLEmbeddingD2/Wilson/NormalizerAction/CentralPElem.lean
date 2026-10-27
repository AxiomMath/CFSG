module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup

section

variable {L : Type*} [Group L] [Finite L]

open scoped IsMulCommutative in
theorem eq_one_of_mem_center_of_abelian (hperf : Group.IsPerfect L) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L) [IsMulCommutative P] {z : L} (hz : z ∈ center L) (hzP : z ∈ (P : Subgroup L)) :
    z = 1 := by
  have key : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup L) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have hc : z ^ k ∈ center L := (center L).pow_mem hz k
    rw [mem_center_iff] at hc
    rw [hc g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hV := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup L)) z key
  have hone : MonoidHom.transfer (MonoidHom.id (P : Subgroup L)) z = 1 := by
    have hz' : z ∈ commutator L := Group.IsPerfect.mem_commutator
    have := Abelianization.commutator_subset_ker (MonoidHom.transfer (MonoidHom.id (P : Subgroup L))) hz'
    exact this
  rw [hone] at hV
  have hpow : z ^ (P : Subgroup L).index = 1 := by
    have := congrArg Subtype.val hV
    simpa using this.symm
  have hord' : orderOf z ∣ Nat.card (P : Subgroup L) := Subgroup.orderOf_dvd_natCard _ hzP
  have hdvd : orderOf z ∣ (P : Subgroup L).index := orderOf_dvd_of_pow_eq_one hpow
  have hcop := P.card_coprime_index
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hord' hdvd)

theorem eq_one_of_mem_center_of_cyclic_quotient {Q : Type*} [Group Q]
    (hperf : Group.IsPerfect L) {p : ℕ} [Fact p.Prime] (π : L →* Q) (hker : π.ker ≤ center L)
    (hQ : ∀ S : Subgroup Q, IsPGroup p S → IsCyclic S) {z : L} (hz : z ∈ center L)
    (hzp : orderOf z = p) : z = 1 := by
  have hgrp : IsPGroup p (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzp, pow_one])
  obtain ⟨P, hzP⟩ := hgrp.exists_le_sylow
  have hPp : IsPGroup p (P : Subgroup L) := P.isPGroup'
  have hS : IsCyclic ↥((P : Subgroup L).map π) :=
    hQ _ (hPp.of_surjective (π.subgroupMap (P : Subgroup L)) (π.subgroupMap_surjective _))
  have hker' : (π.subgroupMap (P : Subgroup L)).ker ≤ center ↥(P : Subgroup L) := by
    intro x hx
    have hx1 : π (x : L) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa using this
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hx1)) (g : L))
  haveI : IsMulCommutative ↥(P : Subgroup L) :=
    (π.subgroupMap (P : Subgroup L)).isMulCommutative_of_isCyclic_of_ker_le_center hker'
  exact eq_one_of_mem_center_of_abelian hperf P hz (hzP (mem_zpowers z))

end

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
