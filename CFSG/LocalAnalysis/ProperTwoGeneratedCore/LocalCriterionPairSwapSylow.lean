module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

universe u

variable {K : Type u} [Group K] [Finite K]

omit [Finite K] in
theorem commuting_involutions_mem_common_sylow
    {u t : K} (hu : IsInvolution u) (ht : IsInvolution t) (hut : Commute u t) :
    ∃ P : Sylow 2 K, u ∈ (P : Subgroup K) ∧ t ∈ (P : Subgroup K) := by
  have huP : IsPGroup 2 (Subgroup.zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have htP : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht.sq_eq_one ht.ne_one
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers t) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor <;> intro hy
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      exact ⟨n, by rw [hut.zpow_zpow m n, mul_inv_cancel_right]⟩
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      change t ^ n = u ^ m * y * (u ^ m)⁻¹ at hn
      calc
        t ^ n = (u ^ m)⁻¹ * (u ^ m * t ^ n) := by group
        _ = (u ^ m)⁻¹ * (t ^ n * u ^ m) := by rw [(hut.zpow_zpow m n).eq]
        _ = (u ^ m)⁻¹ * ((u ^ m * y * (u ^ m)⁻¹) * u ^ m) := by rw [hn]
        _ = y := by group
  have hsup : IsPGroup 2
      (Subgroup.zpowers u ⊔ Subgroup.zpowers t : Subgroup K) :=
    IsPGroup.to_sup_of_normal_right' huP htP hnorm
  obtain ⟨P, hle⟩ := IsPGroup.exists_le_sylow hsup
  exact ⟨P, hle ((show Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers t
      from le_sup_left) (Subgroup.mem_zpowers u)),
    hle ((show Subgroup.zpowers t ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers t
      from le_sup_right) (Subgroup.mem_zpowers t))⟩

theorem involution_conjugate_mem_sylow
    (P : Sylow 2 K) {s : K} (hs : IsInvolution s) :
    ∃ g : K, g * s * g⁻¹ ∈ (P : Subgroup K) := by
  have hsP : IsPGroup 2 (Subgroup.zpowers s) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hs.sq_eq_one hs.ne_one
  obtain ⟨Q, hle⟩ := IsPGroup.exists_le_sylow hsP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  refine ⟨g, ?_⟩
  have hmem : g * s * g⁻¹ ∈ ((g • Q : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Set.mem_smul_set.mpr ⟨s, hle (Subgroup.mem_zpowers s), rfl⟩
  rwa [hg] at hmem

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
