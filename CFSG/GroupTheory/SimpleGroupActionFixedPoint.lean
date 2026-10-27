module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GroupTheory

open MulAction

theorem exists_fixed_of_card_eq_168 {Γ X : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    [MulAction Γ X] (hΓ : Nat.card Γ = 168) (hX : Nat.card X = 8) (x₀ : X)
    (h2 : 2 ∣ Nat.card (MulAction.stabilizer Γ x₀)) : ∃ x : X, ∀ g : Γ, g • x = x := by
  classical
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  set O := MulAction.orbit Γ x₀ with hO
  set k := Nat.card O with hk
  haveI : Nonempty O := ⟨⟨x₀, MulAction.mem_orbit_self x₀⟩⟩
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hkpos : 0 < k := hOpos
  have hindex : (MulAction.stabilizer Γ x₀).index = k := by
    rw [MulAction.index_stabilizer, hk, ← hO]
    exact (Nat.card_coe_set_eq O).symm
  have hk_mul : k * Nat.card (MulAction.stabilizer Γ x₀) = 168 := by
    rw [← hindex, mul_comm, ← hΓ]
    exact (MulAction.stabilizer Γ x₀).card_mul_index
  obtain ⟨r, hr⟩ := h2
  have hkr : k * r = 84 := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    calc 2 * (k * r) = k * (2 * r) := by ring
      _ = k * Nat.card (MulAction.stabilizer Γ x₀) := by rw [hr]
      _ = 168 := hk_mul
      _ = 2 * 84 := by norm_num
  have hk_le : k ≤ 8 := by
    rw [hk, ← hX]
    exact Nat.card_le_card_of_injective (f := (Subtype.val : O → X)) Subtype.val_injective
  have hk_dvd : k ∣ 84 := ⟨r, hkr.symm⟩
  have hnot : ¬ (2 ≤ k ∧ k ≤ 6) := by
    rintro ⟨h2k, h6⟩
    have hproper : MulAction.stabilizer Γ x₀ ≠ ⊤ := by
      intro htop
      rw [htop, Subgroup.index_top] at hindex
      omega
    have hcore : (MulAction.stabilizer Γ x₀).normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (MulAction.stabilizer Γ x₀).normalCore with h | h
      · exact h
      · exact absurd (top_le_iff.mp (h ▸ (MulAction.stabilizer Γ x₀).normalCore_le)) hproper
    have hdvd : Nat.card Γ ∣ k.factorial := by
      have h := (MulAction.stabilizer Γ x₀).index_normalCore_dvd_factorial_index
      rwa [hcore, Subgroup.index_bot, hindex] at h
    rw [hΓ] at hdvd
    interval_cases k <;> exact absurd hdvd (by decide)
  have hk17 : k = 1 ∨ k = 7 := by
    interval_cases k <;> (first | omega | norm_num at hk_dvd)
  rcases hk17 with hk1 | hk7
  · refine ⟨x₀, fun g => ?_⟩
    have hsub : Subsingleton O := (Nat.card_eq_one_iff_unique.mp (by rw [← hk]; exact hk1)).1
    have := hsub.elim (⟨g • x₀, MulAction.mem_orbit x₀ g⟩ : O) ⟨x₀, MulAction.mem_orbit_self x₀⟩
    exact congrArg Subtype.val this
  · have hOcard : O.ncard = 7 := by
      calc O.ncard = Nat.card ↥O := (Nat.card_coe_set_eq O).symm
        _ = k := hk.symm
        _ = 7 := hk7
    have hlt : O.ncard < (Set.univ : Set X).ncard := by
      rw [hOcard, Set.ncard_univ, hX]
      norm_num
    obtain ⟨y, -, hyO⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt (Set.toFinite _)
    have hcomp : (Oᶜ : Set X).ncard = 1 := by
      rw [Set.ncard_compl, hOcard, hX]
    have hsub : MulAction.orbit Γ y ⊆ Oᶜ := by
      intro z hz
      rw [Set.mem_compl_iff]
      intro hzO
      apply hyO
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hz
      obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hzO
      rw [← hg] at hh
      refine MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * h, ?_⟩
      calc (g⁻¹ * h) • x₀ = g⁻¹ • (h • x₀) := mul_smul _ _ _
        _ = g⁻¹ • (g • y) := by rw [hh]
        _ = y := inv_smul_smul _ _
    have h1 : Nat.card (MulAction.orbit Γ y) ≤ 1 := by
      rw [Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (le_of_eq hcomp)
    haveI : Nonempty (MulAction.orbit Γ y) := ⟨⟨y, MulAction.mem_orbit_self y⟩⟩
    have h1' : Nat.card (MulAction.orbit Γ y) = 1 := by
      have hp : 0 < Nat.card (MulAction.orbit Γ y) := Nat.card_pos
      omega
    refine ⟨y, fun g => ?_⟩
    have hsubs : Subsingleton (MulAction.orbit Γ y) :=
      (Nat.card_eq_one_iff_unique.mp h1').1
    have := hsubs.elim (⟨g • y, MulAction.mem_orbit y g⟩ : MulAction.orbit Γ y)
      ⟨y, MulAction.mem_orbit_self y⟩
    exact congrArg Subtype.val this

end CFSG.GroupTheory
