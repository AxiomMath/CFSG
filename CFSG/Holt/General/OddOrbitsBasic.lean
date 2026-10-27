module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Holt.General.Defs
public import CFSG.LocalAnalysis.ComponentClassification.LBalancePrimeCore

public section

namespace CFSG.Holt.General.OddOrbits

open MulAction Subgroup CFSG.ComponentClassification

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section Index2

variable {B : Subgroup G} [B.Normal] {z : G}

theorem sq_mem (hz : z ^ 2 = 1) (hG : B ⊔ zpowers z = ⊤) (g : G) : g ^ 2 ∈ B := by
  obtain ⟨b, hb, w, hw, rfl⟩ := mem_sup_of_normal_left.mp (hG ▸ mem_top g : g ∈ B ⊔ zpowers z)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have hw2 : z ^ k * z ^ k = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ← pow_two, hz, one_zpow]
  have hsq : (b * z ^ k) ^ 2 = b * (z ^ k * b * (z ^ k)⁻¹) * (z ^ k * z ^ k) := by
    rw [pow_two]; group
  rw [hsq, hw2, mul_one]
  exact B.mul_mem hb (Normal.conj_mem inferInstance b hb _)

theorem pPrimeCore_le [Finite G] (hz : z ^ 2 = 1) (hG : B ⊔ zpowers z = ⊤) :
    CFSG.pPrimeCore 2 G ≤ B := by
  intro x hx
  obtain ⟨k, hk⟩ := Nat.coprime_two_left.mp
    ((CFSG.pPrimeCore_coprime_card (p := 2) (G := G)).coprime_dvd_right
      ((CFSG.pPrimeCore 2 G).orderOf_dvd_natCard hx))
  have hx' : (x ^ 2) ^ (k + 1) = x := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [← hx']
  exact B.pow_mem (sq_mem hz hG x) _

theorem oddCoreOf_eq_pPrimeCore [Finite G] (hz : z ^ 2 = 1) (hG : B ⊔ zpowers z = ⊤) :
    oddCoreOf B = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val ≠ 2}
    (Normal.isSubnormal ‹B.Normal›)
  rw [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore] at h
  rw [oddCoreOf, h, inf_eq_right.mpr (pPrimeCore_le hz hG)]

end Index2

variable [Finite G]

end CFSG.Holt.General.OddOrbits
