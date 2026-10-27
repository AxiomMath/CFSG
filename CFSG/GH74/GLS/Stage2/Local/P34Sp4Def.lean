module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.Stage12.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

structure Sp4Setting {X : Type} [Group X] (K : Subgroup X) (q : ℕ) (u : X) : Prop where
  normal : K.Normal
  psp4 : IVK.IsPSp4 ↥K q
  odd : Odd q
  gt3 : 3 < q
  cen : centralizer (K : Set X) ≤ K
  mem : u ∈ K
  inv : orderOf u = 2
  central : ∃ P : Sylow 2 X, u ∈ (P : Subgroup X) ∧ ∀ s ∈ (P : Subgroup X), s * u = u * s
  big : ∃ P : Subgroup X, P ≤ K ⊓ centralizer ({u} : Set X) ∧ ⁅P, P⁆ = P ∧ q * (q ^ 2 - 1) / 2 < Nat.card ↥P

@[expose] def Sp4Fusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (q : ℕ) (u : X), Sp4Setting K q u →
    ∀ x : X, ∃ k ∈ K, x * u * x⁻¹ = k * u * k⁻¹

@[expose] def Sp4Max : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (q : ℕ) (u : X), Sp4Setting K q u →
    IsCoatom ((centralizer ({u} : Set X)).subgroupOf K)

@[expose] def Sp4OddCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (q : ℕ) (u : X), Sp4Setting K q u →
    pPrimeCore 2 ↥(centralizer ({u} : Set X)) = ⊥

structure Sp4Facts : Prop where
  fusion : Sp4Fusion
  max : Sp4Max
  oddCore : Sp4OddCore

section Gen

variable {X : Type} [Group X]

theorem isCoatom_centralizer_of_fusion {K : Subgroup X} {u : X}
    (hfus : ∀ x : X, ∃ k ∈ K, x * u * x⁻¹ = k * u * k⁻¹)
    (hmax : IsCoatom ((centralizer ({u} : Set X)).subgroupOf K)) :
    IsCoatom (centralizer ({u} : Set X)) := by
  have hfac : ∀ x : X, ∃ k ∈ K, ∃ c ∈ centralizer ({u} : Set X), x = k * c := by
    intro x
    obtain ⟨k, hk, hkx⟩ := hfus x
    refine ⟨k, hk, k⁻¹ * x, ?_, by group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k⁻¹ * x * u = k⁻¹ * (x * u * x⁻¹) * x := by group
      _ = k⁻¹ * (k * u * k⁻¹) * x := by rw [hkx]
      _ = u * (k⁻¹ * x) := by group
  refine ⟨?_, fun M hM => ?_⟩
  · intro htop
    apply hmax.1
    rw [htop, Subgroup.top_subgroupOf]
  · have hle : (centralizer ({u} : Set X)).subgroupOf K ≤ M.subgroupOf K := fun a ha =>
      Subgroup.mem_subgroupOf.2 (hM.le (Subgroup.mem_subgroupOf.1 ha))
    rcases (hmax.le_iff.1 hle) with htop | heq
    · rw [eq_top_iff]
      intro x _
      obtain ⟨k, hk, c, hc, rfl⟩ := hfac x
      have hkM : k ∈ M := by
        have : (⟨k, hk⟩ : ↥K) ∈ M.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 this
      exact M.mul_mem hkM (hM.le hc)
    · exfalso
      apply hM.2
      intro m hm
      obtain ⟨k, hk, c, hc, rfl⟩ := hfac m
      have hkM : k ∈ M := by
        have : k = (k * c) * c⁻¹ := by group
        rw [this]
        exact M.mul_mem hm (M.inv_mem (hM.le hc))
      have : (⟨k, hk⟩ : ↥K) ∈ (centralizer ({u} : Set X)).subgroupOf K := by
        rw [← heq]
        exact Subgroup.mem_subgroupOf.2 hkM
      exact (centralizer ({u} : Set X)).mul_mem (Subgroup.mem_subgroupOf.1 this) hc

theorem eq_bot_of_odd_normal_of_oddCore {Y : Type} [Group Y] [Finite Y] (hY : pPrimeCore 2 Y = ⊥)
    {N : Subgroup Y} [N.Normal] (hN : ∀ n ∈ N, Odd (orderOf n)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥N) := by
    by_contra h
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h))
    have := hN n.1 n.2
    rw [Subgroup.orderOf_coe, hn] at this
    exact absurd this (by decide)
  have hle : N ≤ pPrimeCore 2 Y := le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hodd⟩
  rw [hY] at hle
  exact le_bot_iff.1 hle

end Gen

end CFSG.GH74.GLS.Stage2.Local.P34
