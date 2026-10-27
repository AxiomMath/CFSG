module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicSylowOddComplement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH4

open Subgroup

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {ζ : G} (h : ζ * ζ = 1) (h1 : ζ ≠ 1)
    {u : G} (hu : u ∈ zpowers ζ) : u = 1 ∨ u = ζ := by
  have hord : orderOf ζ = 2 := orderOf_eq_prime (by rwa [sq]) h1
  obtain ⟨k, rfl⟩ := hu
  change ζ ^ k = 1 ∨ ζ ^ k = ζ
  have hk := zpow_mod_orderOf ζ k
  rw [hord] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left
    rw [← hk]
    have : (k % ((2 : ℕ) : ℤ)) = 0 := by exact_mod_cast h0
    rw [this, zpow_zero]
  · right
    rw [← hk]
    have : (k % ((2 : ℕ) : ℤ)) = 1 := by exact_mod_cast h0
    rw [this, zpow_one]

theorem exists_odd_characteristic_isComplement {G : Type*} [Group G] [Finite G] {ζ : G}
    (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (hU : ∀ U : Subgroup G, IsPGroup 2 U → U ≤ centralizer ({ζ} : Set G) → Nat.card U ≤ 2) :
    ∃ N : Subgroup G, N.Characteristic ∧ Odd (Nat.card N) ∧ N.IsComplement' (zpowers ζ) := by
  have hord : orderOf ζ = 2 := orderOf_eq_prime (by rwa [sq]) hζ1
  have hcz : Nat.card (zpowers ζ) = 2 := by rw [Nat.card_zpowers, hord]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpz : IsPGroup 2 (zpowers ζ) := IsPGroup.of_card (n := 1) (by rw [hcz]; rfl)
  obtain ⟨S, hS⟩ := hpz.exists_le_sylow
  have hζS : ζ ∈ (S : Subgroup G) := hS (mem_zpowers ζ)
  have hζc : ζ ∈ centralizer ({ζ} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hUp : IsPGroup 2 ((S : Subgroup G) ⊓ centralizer ({ζ} : Set G) : Subgroup G) :=
    S.isPGroup'.to_inf_left
  have hUeq : zpowers ζ = (S : Subgroup G) ⊓ centralizer ({ζ} : Set G) :=
    eq_of_le_of_card_ge (le_inf hS (zpowers_le.2 hζc)) (by rw [hcz]; exact hU _ hUp inf_le_right)
  have hnt : Nontrivial (S : Subgroup G) :=
    ⟨⟨⟨ζ, hζS⟩, 1, fun h => hζ1 (congrArg Subtype.val h)⟩⟩
  have hcn : Nontrivial (center (S : Subgroup G)) := S.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : center (S : Subgroup G))
  have hcζ : ((c : (S : Subgroup G)) : G) * ζ = ζ * ((c : (S : Subgroup G)) : G) := by
    have := (mem_center_iff.1 c.2) ⟨ζ, hζS⟩
    exact (congrArg Subtype.val this).symm
  have hcU : ((c : (S : Subgroup G)) : G) ∈ zpowers ζ := by
    rw [hUeq]
    exact mem_inf.2 ⟨(c : (S : Subgroup G)).2, mem_centralizer_singleton_iff.2 hcζ⟩
  have hcζ' : ((c : (S : Subgroup G)) : G) = ζ := by
    rcases eq_one_or_eq_of_mem_zpowers hζ2 hζ1 hcU with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hc1
    · exact h
  have hSle : (S : Subgroup G) ≤ centralizer ({ζ} : Set G) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    have := (mem_center_iff.1 c.2) ⟨s, hs⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [hcζ'] at h2
    exact h2
  have hSz : (S : Subgroup G) = zpowers ζ :=
    le_antisymm (by rw [hUeq]; exact le_inf le_rfl hSle) hS
  have hcyc : IsCyclic (S : Subgroup G) := by rw [hSz]; infer_instance
  have heven : Even (Nat.card G) := even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard ζ)
  have hcomp := CFSG.DisconnectedInvolutionGraph.Helpers.cyclic_two_sylow_oddCore_complement S
    hcyc heven
  rw [hSz] at hcomp
  exact ⟨_, CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_characteristic,
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd, hcomp⟩

theorem normal_eq_zpowers {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal] {ζ : X}
    (hζK : ζ ∈ K) (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (hU : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ K → U ≤ centralizer ({ζ} : Set X) →
      Nat.card U ≤ 2)
    (hX : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) : K = zpowers ζ := by
  have hord : orderOf ζ = 2 := orderOf_eq_prime (by rwa [sq]) hζ1
  have hζ'2 : (⟨ζ, hζK⟩ : K) * ⟨ζ, hζK⟩ = 1 := Subtype.ext hζ2
  have hζ'1 : (⟨ζ, hζK⟩ : K) ≠ 1 := fun h => hζ1 (congrArg Subtype.val h)
  have hU' : ∀ U : Subgroup K, IsPGroup 2 U → U ≤ centralizer ({(⟨ζ, hζK⟩ : K)} : Set K) →
      Nat.card U ≤ 2 := by
    intro U hUp hUc
    have h2 := hU (U.map K.subtype) (hUp.map _) (map_subtype_le U) (by
      rintro _ ⟨u, hu, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hUc hu)))
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h2
  obtain ⟨N, hNchar, hNodd, hNcomp⟩ := exists_odd_characteristic_isComplement hζ'2 hζ'1 hU'
  have hN1 : N.map K.subtype = ⊥ := by
    apply hX
    · refine ⟨fun n hn g => ?_⟩
      obtain ⟨n0, hn0, rfl⟩ := hn
      refine ⟨(MulAut.conjNormal g : MulAut K) n0, ?_, ?_⟩
      · exact (characteristic_iff_le_comap.1 hNchar _) hn0
      · simp [MulAut.conjNormal_apply]
    · rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hN0 : N = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at hN1
    exact le_bot_iff.1 hN1
  have hKcard : Nat.card K = 2 := by
    have h := hNcomp.card_mul_card
    rw [hN0, Subgroup.card_bot, one_mul, Nat.card_zpowers,
      show orderOf (⟨ζ, hζK⟩ : K) = 2 from orderOf_eq_prime (by rwa [sq]) hζ'1] at h
    exact h.symm
  exact (eq_of_le_of_card_ge (zpowers_le.2 hζK)
    (by rw [Nat.card_zpowers, hord]; exact hKcard.le)).symm

theorem conj_eq_of_normal {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal] {ζ : X}
    (hζK : ζ ∈ K) (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1)
    (hU : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ K → U ≤ centralizer ({ζ} : Set X) →
      Nat.card U ≤ 2)
    (hX : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) (x : X) :
    x * ζ * x⁻¹ = ζ := by
  have hK := normal_eq_zpowers K hζK hζ2 hζ1 hU hX
  have hmem : x * ζ * x⁻¹ ∈ zpowers ζ := hK ▸ Normal.conj_mem inferInstance ζ hζK x
  rcases eq_one_or_eq_of_mem_zpowers hζ2 hζ1 hmem with h | h
  · exact absurd (by simpa using h) hζ1
  · exact h

end CFSG.EvenSporadicStandard.M24Std.CResH4
