module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem exists_odd_normal_complement {P : Type} [Group P] [Finite P] {z : P}
    (hz : z ∈ center P) (hz2 : orderOf z = 2) {R : Subgroup P} [R.Normal] (hzR : z ∈ R)
    {m : ℕ} (hcard : Nat.card R = 2 * m) (hm : Odd m) :
    ∃ O : Subgroup P, O.Normal ∧ O ≤ R ∧ Nat.card O = m ∧ O ⊓ zpowers z = ⊥ ∧
      O ⊔ zpowers z = R := by
  have hzle : zpowers z ≤ R := Subgroup.zpowers_le.2 hzR
  have hzcenter : zpowers z ≤ Subgroup.center P := Subgroup.zpowers_le.2 hz
  haveI hzpnormal : (zpowers z).Normal := Subgroup.normal_of_le_center hzcenter
  let ZR : Subgroup R := (zpowers z).subgroupOf R
  have hZRcenter : ZR ≤ Subgroup.center R := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : P) * (x : P) = (x : P) * (y : P)
    have hxzp : (x : P) ∈ Subgroup.zpowers z := hx
    have hxzc : (x : P) ∈ Subgroup.center P := hzcenter hxzp
    rw [Subgroup.mem_center_iff] at hxzc
    exact hxzc (y : P)
  haveI : ZR.Normal := Subgroup.normal_of_le_center hZRcenter
  have hZRcard : Nat.card ZR = 2 := by
    change Nat.card ((zpowers z).subgroupOf R) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers, hz2]
  have hZRindex : ZR.index = m := by
    have h := ZR.card_mul_index
    rw [hZRcard, hcard] at h
    exact Nat.mul_left_cancel (by norm_num) h
  have hcop : Nat.Coprime (Nat.card ZR) ZR.index := by
    rw [hZRcard, hZRindex]
    exact Nat.coprime_two_left.2 hm
  obtain ⟨O', hO'⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have hO'card : Nat.card O' = m := by
    have h := hO'.card_mul_card
    rw [hZRcard, hcard, Nat.mul_comm 2 m] at h
    exact Nat.mul_right_cancel (by norm_num) h
  have hchar : ∀ x : R, x ∈ O' ↔ (x : P) ^ m = 1 := by
    intro x
    constructor
    · intro hx
      have h1 : (x : R) ^ m = 1 := by
        have h := pow_card_eq_one' (G := O') (x := ⟨x, hx⟩)
        rw [hO'card] at h
        simpa using Subtype.ext_iff.mp h
      simpa using congrArg (fun y : R => (y : P)) h1
    · intro hx
      have hxR : x ^ m = 1 := by
        apply R.subtype_injective
        rw [map_pow]
        simpa using hx
      obtain ⟨⟨o, z0⟩, hoz, -⟩ := hO'.existsUnique x
      have hcomm : Commute (o : R) (z0 : R) := by
        have hzc := hZRcenter z0.2
        rw [Subgroup.mem_center_iff] at hzc
        exact hzc (o : R)
      have ho_m : (o : R) ^ m = 1 := by
        have h := pow_card_eq_one' (G := O') (x := o)
        rw [hO'card] at h
        simpa using Subtype.ext_iff.mp h
      have hz0_m : (z0 : R) ^ m = (z0 : R) := by
        obtain ⟨k, hk⟩ := hm
        have hz02 : (z0 : R) ^ 2 = 1 := by
          have h := pow_card_eq_one' (G := ZR) (x := z0)
          rw [hZRcard] at h
          simpa using Subtype.ext_iff.mp h
        rw [hk, pow_succ, pow_mul, hz02, one_pow, one_mul]
      have hxpow : x ^ m = (z0 : R) := by
        rw [← hoz]
        rw [hcomm.mul_pow, ho_m, hz0_m, one_mul]
      have hz01 : (z0 : R) = 1 := by rw [← hxpow, hxR]
      have hxeq : x = (o : R) := by rw [← hoz, hz01, mul_one]
      rw [hxeq]
      exact o.2
  refine ⟨O'.map R.subtype, ?_, Subgroup.map_subtype_le O', ?_, ?_, ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_map] at hn ⊢
    obtain ⟨o, ho, rfl⟩ := hn
    have hmem : g * (o : P) * g⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem (o : P) o.2 g
    let y : R := ⟨g * (o : P) * g⁻¹, hmem⟩
    have hyO' : y ∈ O' := by
      rw [hchar y]
      show (g * (o : P) * g⁻¹) ^ m = 1
      rw [conj_pow]
      have hoP : (o : P) ^ m = 1 := (hchar o).1 ho
      rw [hoP, mul_one, mul_inv_cancel]
    exact Subgroup.mem_map_of_mem R.subtype hyO'
  · rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact hO'card
  · apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨hxO, hxz⟩ := hx
    obtain ⟨o, ho, hox⟩ := Subgroup.mem_map.mp hxO
    have hxO' : (⟨x, hzle hxz⟩ : R) ∈ O' := by
      have hxo : (⟨x, hzle hxz⟩ : R) = o := by
        apply Subtype.ext
        exact hox.symm
      rw [hxo]
      exact ho
    have hxZR : (⟨x, hzle hxz⟩ : R) ∈ ZR := hxz
    have hmem : (⟨x, hzle hxz⟩ : R) ∈ (⊥ : Subgroup R) := by
      have : (⟨x, hzle hxz⟩ : R) ∈ O' ⊓ ZR := ⟨hxO', hxZR⟩
      rwa [disjoint_iff.mp hO'.disjoint] at this
    refine Subgroup.mem_bot.mpr ?_
    simpa using congrArg (fun y : R => (y : P)) (Subgroup.mem_bot.mp hmem)
  · apply le_antisymm
    · rw [sup_le_iff]
      exact ⟨Subgroup.map_subtype_le O', hzle⟩
    · intro x hx
      obtain ⟨⟨o, z0⟩, hoz, -⟩ := hO'.existsUnique ⟨x, hx⟩
      refine (Subgroup.mem_sup_of_normal_right (s := O'.map R.subtype) (t := zpowers z)).2
        ⟨(o : P), Subgroup.mem_map_of_mem R.subtype o.2, (z0 : P),
          show (z0 : P) ∈ zpowers z from z0.2, ?_⟩
      simpa using congrArg (fun y : R => (y : P)) hoz

end CFSG.OddStandard.SmallF3.Omega
