module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Local.PrimeFreeFactorDerivedOrder
import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import Mathlib.Data.Rat.Floor

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {π : Set ℕ} {K L P : Subgroup X}

theorem commutator_eq_subgroupOf_commutator (L : Subgroup X) :
    _root_.commutator ↥L = ⁅L, L⁆.subgroupOf L := by
  rw [Subgroup.subgroupOf, ← Subgroup.map_subtype_commutator L,
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

theorem commutator_le_sup_commutator (hK : K.Normal) (hKL : K ⊔ L = ⊤) :
    _root_.commutator X ≤ K ⊔ ⁅L, L⁆ := by
  have := hK
  have hsurj : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  have hLtop : Subgroup.map (QuotientGroup.mk' K) L = ⊤ := by
    have h : Subgroup.map (QuotientGroup.mk' K) (K ⊔ L) = ⊤ := by
      rw [hKL]; exact Subgroup.map_top_of_surjective _ hsurj
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h
  have himage : Subgroup.map (QuotientGroup.mk' K) (_root_.commutator X)
      = Subgroup.map (QuotientGroup.mk' K) ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_commutator, hLtop,
      Subgroup.map_top_of_surjective _ hsurj]
  calc _root_.commutator X ≤ Subgroup.comap (QuotientGroup.mk' K)
        (Subgroup.map (QuotientGroup.mk' K) (_root_.commutator X)) := Subgroup.le_comap_map _ _
    _ = ⁅L, L⁆ ⊔ K := by rw [himage, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    _ = K ⊔ ⁅L, L⁆ := sup_comm _ _

theorem IsPiSubgroup.inf_commutator_le_commutator [Finite X] (hP : IsPiSubgroup π P)
    (hK : K.Normal) (hKπ : ∀ p ∈ (Nat.card K).primeFactors, p ∉ π)
    (hKL : (K : Set X) * (L : Set X) = Set.univ) (hPL : P ≤ L) :
    P ⊓ _root_.commutator X ≤ ⁅L, L⁆ := by
  have := hK
  have hsup : K ⊔ L = ⊤ := coe_mul_coe_eq_univ_iff_sup_eq_top.mp hKL
  intro x hx
  obtain ⟨hxP, hxX'⟩ := hx
  have hxL : x ∈ L := hPL hxP
  have hmem : x ∈ K ⊔ ⁅L, L⁆ := commutator_le_sup_commutator hK hsup hxX'
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨k, hk, l, hl, hkl⟩ := hmem
  have hlL : l ∈ L := Subgroup.commutator_le_self L hl
  have hkL : k ∈ L := by
    have hkeq : k = x * l⁻¹ := by rw [← hkl]; group
    rw [hkeq]; exact L.mul_mem hxL (L.inv_mem hlL)
  set ρ := QuotientGroup.mk' (_root_.commutator ↥L)
  have hlmem : (⟨l, hlL⟩ : ↥L) ∈ _root_.commutator ↥L := by
    rw [commutator_eq_subgroupOf_commutator, Subgroup.mem_subgroupOf]; exact hl
  have hρl : ρ ⟨l, hlL⟩ = 1 := by
    rw [← QuotientGroup.ker_mk' (_root_.commutator ↥L)] at hlmem
    exact hlmem
  have hxeq : (⟨x, hxL⟩ : ↥L) = ⟨k, hkL⟩ * ⟨l, hlL⟩ := by
    apply Subtype.ext; simpa using hkl.symm
  have hρx : ρ ⟨x, hxL⟩ = ρ ⟨k, hkL⟩ := by rw [hxeq, map_mul, hρl, mul_one]
  have hd1 : orderOf (ρ ⟨x, hxL⟩) ∣ orderOf x := by
    have h := orderOf_map_dvd ρ (⟨x, hxL⟩ : ↥L)
    rwa [Subgroup.orderOf_mk] at h
  have hd2 : orderOf (ρ ⟨x, hxL⟩) ∣ orderOf k := by
    rw [hρx]
    have h := orderOf_map_dvd ρ (⟨k, hkL⟩ : ↥L)
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime (orderOf x) (orderOf k) := by
    rw [← Nat.disjoint_primeFactors (orderOf_pos x).ne' (orderOf_pos k).ne', Finset.disjoint_left]
    intro p hp hp'
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpπ : p ∈ π := by
      refine isPiSubgroup_iff.mp hP p (Nat.mem_primeFactors.2 ⟨hpp, ?_, Nat.card_pos.ne'⟩)
      exact (Nat.dvd_of_mem_primeFactors hp).trans (P.orderOf_dvd_natCard hxP)
    refine hKπ p (Nat.mem_primeFactors.2 ⟨hpp, ?_, Nat.card_pos.ne'⟩) hpπ
    exact (Nat.dvd_of_mem_primeFactors hp').trans (K.orderOf_dvd_natCard hk)
  have hone : orderOf (ρ ⟨x, hxL⟩) = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hxmem : (⟨x, hxL⟩ : ↥L) ∈ _root_.commutator ↥L := by
    rw [← QuotientGroup.ker_mk' (_root_.commutator ↥L)]
    exact orderOf_eq_one_iff.1 hone
  rw [commutator_eq_subgroupOf_commutator, Subgroup.mem_subgroupOf] at hxmem
  exact hxmem

theorem IsPiSubgroup.inf_closure_le_closure [Finite X] (hP : IsPiSubgroup π P) (hK : K.Normal)
    (hKπ : ∀ p ∈ (Nat.card K).primeFactors, p ∉ π)
    (hKL : (K : Set X) * (L : Set X) = Set.univ) (hPL : P ≤ L) :
    P ⊓ Subgroup.closure {g : X | ∃ x y : X, x⁻¹ * y⁻¹ * x * y = g} ≤
      Subgroup.closure {g : X | ∃ a ∈ L, ∃ b ∈ L, a⁻¹ * b⁻¹ * a * b = g} := by
  rw [closure_setOf_inv_mul_inv_mul_mul_eq_commutator, closure_setOf_inv_mul_inv_mul_mul]
  exact hP.inf_commutator_le_commutator hK hKπ hKL hPL

end

end CFSG.FeitThompson
