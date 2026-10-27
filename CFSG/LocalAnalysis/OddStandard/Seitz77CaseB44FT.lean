module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

theorem perfect_le_closure_conj_sylow {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hM : ⁅M, M⁆ = M) (hT : IsSylowOf 2 T M) :
    M ≤ Subgroup.closure {y : G | ∃ m ∈ M, ∃ s ∈ T, y = m * s * m⁻¹} := by
  set S : Set G := {y : G | ∃ m ∈ M, ∃ s ∈ T, y = m * s * m⁻¹} with hS
  set C : Subgroup G := Subgroup.closure S with hC
  have hTM : T ≤ M := hT.le
  have hCM : C ≤ M := by
    refine (Subgroup.closure_le M).mpr ?_
    rintro y ⟨m, hm, s, hs, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hTM hs)) (M.inv_mem hm)
  have hTC : T ≤ C := by
    intro s hs
    refine Subgroup.subset_closure ⟨1, M.one_mem, s, hs, ?_⟩
    simp
  have hconj : ∀ g ∈ M, ∀ h ∈ C, g * h * g⁻¹ ∈ C := by
    intro g hg h hh
    have hh' : h ∈ Subgroup.closure S := hh
    clear hh
    induction hh' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm, s, hs, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨g * m, M.mul_mem hg hm, s, hs, ?_⟩
      group
    | one => simp
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact C.mul_mem hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact C.inv_mem hx
  have hnorm : (C.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCM]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj g hg h, fun hh => ?_⟩
    have h1 := hconj g⁻¹ (M.inv_mem hg) _ hh
    have h2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [h2] at h1
  have : (C.subgroupOf M).Normal := hnorm
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.mpr hM
  have hodd : Odd (Nat.card (M ⧸ C.subgroupOf M)) := by
    have h1 : Nat.card (M ⧸ C.subgroupOf M) = C.relIndex M := rfl
    have h2 : ¬ 2 ∣ T.relIndex M := ((isSylowOf_iff).mp hT).2.2
    have h3 : C.relIndex M ∣ T.relIndex M :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex T C M hTC hCM)
    rw [h1, Nat.odd_iff]
    have h4 : ¬ 2 ∣ C.relIndex M := fun h => h2 (h.trans h3)
    omega
  have hsolv : Group.IsSolvable (M ⧸ C.subgroupOf M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : Subsingleton (M ⧸ C.subgroupOf M) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable (M ⧸ C.subgroupOf M) hsolv
  exact Subgroup.subgroupOf_eq_top.mp (QuotientGroup.subgroup_eq_top_of_subsingleton _ hsub)

end CFSG.OddStandard.Seitz77
