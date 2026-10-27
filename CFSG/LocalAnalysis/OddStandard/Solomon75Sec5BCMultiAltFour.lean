module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermLift

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement
open AhatData

section AltFour

variable {n : ℕ}

private theorem bcdAltFour_card_support_le {σ a : Perm (Fin n)} (ha : ∀ x, σ x ≠ x → a x = x) :
    a.support.card ≤ fixCount σ := by
  refine Finset.card_le_card fun x hx => ?_
  rw [Equiv.Perm.mem_support] at hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra h
  exact hx (ha x h)

private theorem bcdAltFour_cycleType {σ a : Perm (Fin n)} (hfix : fixCount σ = 4)
    (ha : a ∈ altFixOf σ) (ha1 : a ≠ 1) (ha2 : a * a = 1) : a.cycleType = {2, 2} := by
  have hle := bcdAltFour_card_support_le ha.1
  rw [hfix] at hle
  obtain ⟨k, hk⟩ : ∃ k, a.cycleType = Multiset.replicate k 2 :=
    ⟨_, Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) (by rw [pow_two]; exact ha2)⟩
  have hsum : 2 * k = a.support.card := by
    rw [← Equiv.Perm.sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ha1 (Equiv.Perm.cycleType_eq_zero.1 (by rw [hk]; rfl))
  have heven : Even k := by
    have h := Equiv.Perm.sign_of_cycleType a
    rw [ha.2, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at h
    have h' : (-1 : ℤˣ) ^ (k * 2 + k) = 1 := h.symm
    rw [neg_one_pow_eq_one_iff_even (by decide)] at h'
    obtain ⟨r, hr⟩ := h'
    exact ⟨r - k, by omega⟩
  obtain ⟨m, hm⟩ := heven
  have hk2 : k = 2 := by omega
  rw [hk, hk2]
  rfl

private theorem bcdAltFour_altFixOf_eq_map (σ : Perm (Fin n)) :
    altFixOf σ = (alternatingGroup {x : Fin n // σ x = x}).map
      (Equiv.Perm.ofSubtype : Perm {x : Fin n // σ x = x} →* Perm (Fin n)) := by
  ext g
  exact (CFSG.ComponentClassification.SymmetricLocal.mem_map_ofSubtype_alternatingGroup_iff
    (p := fun x => σ x = x)).symm

private theorem bcdAltFour_equiv {σ : Perm (Fin n)} (hfix : fixCount σ = 4) :
    Nonempty (↥(altFixOf σ) ≃* alternatingGroup (Fin 4)) := by
  have hcard : Fintype.card {x : Fin n // σ x = x} = 4 := by
    rw [Fintype.card_subtype]
    exact hfix
  exact ⟨(MulEquiv.subgroupCongr (bcdAltFour_altFixOf_eq_map σ)).trans
    ((Subgroup.equivMapOfInjective _ Equiv.Perm.ofSubtype Equiv.Perm.ofSubtype_injective).symm.trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq hcard)))⟩

private theorem bcdAltFour_conj_mem {σ ν a : Perm (Fin n)} (hν : ν * σ = σ * ν)
    (ha : a ∈ altFixOf σ) : ν⁻¹ * a * ν ∈ altFixOf σ := by
  have h : ν * σ * ν⁻¹ = σ := by rw [hν, mul_inv_cancel_right]
  exact (mem_altFixOf_conj σ a ν).1 (by rw [h]; exact ha)

theorem exists_alt4_fixed {σ : Perm (Fin n)} (hfix : fixCount σ = 4) :
    ∃ W₀ : Subgroup (Perm (Fin n)), W₀ ≤ alternatingGroup (Fin n) ∧
      Nonempty (↥W₀ ≃* alternatingGroup (Fin 4)) ∧
      (∀ a ∈ W₀, a ≠ 1 → a * a = 1 → a.cycleType = {2, 2}) ∧ (∀ a ∈ W₀, a * σ = σ * a) ∧
      (∀ ν : Perm (Fin n), ν * σ = σ * ν → ∀ a ∈ W₀, ν * a * ν⁻¹ ∈ W₀) := by
  refine ⟨altFixOf σ, fun a ha => Equiv.Perm.mem_alternatingGroup.2 ha.2, bcdAltFour_equiv hfix,
    fun a ha ha1 ha2 => bcdAltFour_cycleType hfix ha ha1 ha2,
    fun a ha => comm_of_forall_fixed ha.1, fun ν hν a ha => ?_⟩
  have hν' : ν⁻¹ * σ = σ * ν⁻¹ := (show Commute ν σ from hν).inv_left.eq
  simpa only [inv_inv] using bcdAltFour_conj_mem hν' ha

end AltFour

end CFSG.OddStandard.Solomon75
