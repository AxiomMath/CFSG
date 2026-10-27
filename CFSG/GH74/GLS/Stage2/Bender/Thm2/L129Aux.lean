module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L129

section Twist

variable {G : Type*} [Group G]

theorem exists_fixed_of_twist {z r x : G} (hz : z * z = 1) (hx : x = r⁻¹ * (z * r * z⁻¹))
    (hodd : Odd (orderOf x)) : ∃ y ∈ Subgroup.zpowers x, z * (r * y) * z⁻¹ = r * y := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzx : z * x * z⁻¹ = x⁻¹ := by
    have h1 : x⁻¹ = z * r⁻¹ * z * r := by
      rw [hx, hz']
      simp [mul_assoc, hz']
    rw [h1, hx, hz']
    calc z * (r⁻¹ * (z * r * z)) * z = z * r⁻¹ * z * r * (z * z) := by group
      _ = z * r⁻¹ * z * r := by rw [hz, mul_one]
  obtain ⟨k, hk⟩ := hodd
  set y := x ^ (k + 1) with hy
  have hy2 : y * y = x := by
    have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    calc y * y = x ^ (k + 1) * x ^ (k + 1) := rfl
      _ = x ^ (2 * k + 1) * x := by rw [← pow_add, ← pow_succ]; ring_nf
      _ = x := by rw [← hk, h1, one_mul]
  have hzy : z * y * z⁻¹ = y⁻¹ := by
    have : z * x ^ (k + 1) * z⁻¹ = (z * x * z⁻¹) ^ (k + 1) := (conj_pow).symm
    rw [hy, this, hzx, inv_pow]
  refine ⟨y, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_⟩
  have hzr : z * r * z⁻¹ = r * x := by rw [hx]; group
  calc z * (r * y) * z⁻¹ = (z * r * z⁻¹) * (z * y * z⁻¹) := by group
    _ = (r * x) * y⁻¹ := by rw [hzr, hzy]
    _ = r * y := by rw [← hy2]; group

end Twist

section Odd

theorem odd_card_of_forall_odd_orderOf {K : Type*} [Group K] [Finite K]
    (h : ∀ x : K, Odd (orderOf x)) : Odd (Nat.card K) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card K := by
    rwa [Nat.not_odd_iff_even, even_iff_two_dvd] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  have := h x
  rw [hx] at this
  exact absurd this (by decide)

variable {G : Type*} [Group G]

theorem le_pPrimeCoreOf_of_normal_of_odd {H K : Subgroup G} (hKH : K ≤ H)
    (hN : (K.subgroupOf H).Normal) (hodd : Odd (Nat.card K)) : K ≤ pPrimeCoreOf 2 H := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcop : Nat.Coprime 2 (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact (Nat.coprime_two_left).mpr hodd
  have h1 : K.subgroupOf H ≤ pPrimeCore 2 ↥H := le_sSup ⟨hN, hcop⟩
  intro x hx
  exact ⟨⟨x, hKH hx⟩, h1 hx, rfl⟩

end Odd

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L129
