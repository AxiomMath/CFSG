module

public import CFSG.FeitThompson.Definitions.PuigSubgroupIteration
import CFSG.FeitThompson.Local.PuigLambdaComparison
import CFSG.FeitThompson.Local.PuigLimitsStationaryExchange

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {X : Type*} [Group X]

theorem le_map_puigLambda_of_le_normalizer {Y : Subgroup X} {V : Subgroup Y} {A : Subgroup X}
    (hAY : A ≤ Y) (hA : IsMulCommutative A)
    (hnorm : V.map Y.subtype ≤ normalizer (A : Set X)) :
    A ≤ (puigLambda V).map Y.subtype := by
  have hcomm : IsMulCommutative (A.subgroupOf Y) :=
    comap_injective_isMulCommutative (H := A) Y.subtype_injective
  have hnorm' : V ≤ normalizer ((A.subgroupOf Y : Subgroup Y) : Set Y) := by
    intro v hv
    rw [mem_normalizer_iff]
    intro h
    have hv' : (v : X) ∈ normalizer (A : Set X) := hnorm ⟨v, hv, rfl⟩
    rw [mem_normalizer_iff] at hv'
    simpa [mem_subgroupOf] using hv' (h : X)
  calc A = (A.subgroupOf Y).map Y.subtype := (map_subgroupOf_eq_of_le hAY).symm
    _ ≤ (puigLambda V).map Y.subtype := map_mono (le_puigLambda hcomm hnorm')

theorem puigLambda_le_map_puigLambda {Y : Subgroup X} {V : Subgroup Y} {U : Subgroup X}
    (hVU : V.map Y.subtype ≤ U) (hY : puigLambda U ≤ Y) :
    puigLambda U ≤ (puigLambda V).map Y.subtype :=
  puigLambda_le fun _ hA hU =>
    le_map_puigLambda_of_le_normalizer ((le_puigLambda hA hU).trans hY) hA (hVU.trans hU)

theorem map_puigLambda_le_puigLambda_of_le {Y : Subgroup X} {V : Subgroup Y} {U : Subgroup X}
    (hUV : U ≤ V.map Y.subtype) : (puigLambda V).map Y.subtype ≤ puigLambda U :=
  (map_puigLambda_le_puigLambda_map Y.subtype V).trans (puigLambda_antitone hUV)

theorem map_puigSeries_succ_le_puigSeries_succ {Y : Subgroup X} {n : ℕ}
    (ih : puigSeries X n ≤ (puigSeries Y n).map Y.subtype) :
    (puigSeries Y (n + 1)).map Y.subtype ≤ puigSeries X (n + 1) := by
  rw [puigSeries_succ (X := X), puigSeries_succ (X := Y)]
  exact map_puigLambda_le_puigLambda_of_le ih

theorem puigSeries_succ_le_map_puigSeries_succ {Y : Subgroup X} {n : ℕ}
    (ih : (puigSeries Y n).map Y.subtype ≤ puigSeries X n)
    (hY : puigSeries X (n + 1) ≤ Y) :
    puigSeries X (n + 1) ≤ (puigSeries Y (n + 1)).map Y.subtype := by
  rw [puigSeries_succ (X := X), puigSeries_succ (X := Y)]
  refine puigLambda_le_map_puigLambda ih ?_
  rwa [puigSeries_succ] at hY

theorem puigSeries_two_mul_le_of_puigSubgroup_le {Y : Subgroup X} (hL : puigSubgroup X ≤ Y)
    (n : ℕ) : puigSeries X (2 * n) ≤ Y :=
  calc puigSeries X (2 * n) ≤ puigLower X := le_puigLower n
    _ ≤ puigUpper X := puigLower_le_puigUpper
    _ = puigSubgroup X := puigSubgroup_eq_puigUpper.symm
    _ ≤ Y := hL

theorem map_puigSeries_odd_le {Y : Subgroup X} (hL : puigSubgroup X ≤ Y) (n : ℕ) :
    (puigSeries Y (2 * n + 1)).map Y.subtype ≤ puigSeries X (2 * n + 1) := by
  induction n with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, puigSeries_one (X := X)]
    exact le_top
  | succ n ih =>
    have heven : puigSeries X (2 * n + 1 + 1) ≤ (puigSeries Y (2 * n + 1 + 1)).map Y.subtype := by
      refine puigSeries_succ_le_map_puigSeries_succ ih ?_
      have h := puigSeries_two_mul_le_of_puigSubgroup_le hL (n + 1)
      rwa [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring] at h
    have hodd := map_puigSeries_succ_le_puigSeries_succ (Y := Y) (n := 2 * n + 1 + 1) heven
    rwa [show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 from by ring] at hodd

theorem puigSubgroup_le_map_puigSeries_odd {Y : Subgroup X} [Finite X]
    (hL : puigSubgroup X ≤ Y) (n : ℕ) :
    puigSubgroup X ≤ (puigSeries Y (2 * n + 1)).map Y.subtype := by
  induction n with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, puigSeries_one (X := Y), ← MonoidHom.range_eq_map,
      Y.range_subtype]
    exact hL
  | succ n ih =>
    have heven : (puigSeries Y (2 * n + 1 + 1)).map Y.subtype ≤ puigLower X := by
      have h := map_puigLambda_le_puigLambda_of_le (Y := Y) (V := puigSeries Y (2 * n + 1)) ih
      rwa [← puigSeries_succ, puigLambda_puigSubgroup] at h
    have hY : puigLambda (puigLower X) ≤ Y := by
      rw [puigLambda_puigLower, ← puigSubgroup_eq_puigUpper]; exact hL
    have hodd : puigSubgroup X ≤ (puigSeries Y (2 * n + 1 + 1 + 1)).map Y.subtype := by
      have h := puigLambda_le_map_puigLambda heven hY
      rwa [puigLambda_puigLower, ← puigSubgroup_eq_puigUpper, ← puigSeries_succ] at h
    rwa [show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 from by ring] at hodd

theorem map_puigSubgroup_eq_puigSubgroup {Y : Subgroup X} [Finite X]
    (hL : puigSubgroup X ≤ Y) :
    (puigSubgroup Y).map Y.subtype = puigSubgroup X := by
  obtain ⟨r, hr⟩ := exists_puigSeries_two_mul_add_one_eq_puigSubgroup X
  obtain ⟨s, hs⟩ := exists_puigSeries_two_mul_add_one_eq_puigSubgroup (Y : Type _)
  refine le_antisymm ?_ ?_
  · rw [← hr (max r s) (le_max_left r s), ← hs (max r s) (le_max_right r s)]
    exact map_puigSeries_odd_le hL _
  · rw [← hs (max r s) (le_max_right r s)]
    exact puigSubgroup_le_map_puigSeries_odd hL _

theorem puigSubgroup_eq_subgroupOf {Y : Subgroup X} [Finite X] (hL : puigSubgroup X ≤ Y) :
    puigSubgroup Y = (puigSubgroup X).subgroupOf Y := by
  rw [← map_puigSubgroup_eq_puigSubgroup hL, subgroupOf, comap_map_eq_self_of_injective
    Y.subtype_injective]

theorem mem_puigSubgroup_iff_of_puigSubgroup_le {Y : Subgroup X} [Finite X]
    (hL : puigSubgroup X ≤ Y) (y : Y) : y ∈ puigSubgroup Y ↔ (y : X) ∈ puigSubgroup X := by
  rw [puigSubgroup_eq_subgroupOf hL, mem_subgroupOf]

theorem puigSubgroup_puigSubgroup [Finite X] :
    puigSubgroup (puigSubgroup X) = ⊤ := by
  have h := puigSubgroup_eq_subgroupOf (X := X) (Y := puigSubgroup X) le_rfl
  rw [h, subgroupOf_eq_top]

theorem map_puigLower_eq_puigLower {Y : Subgroup X} [Finite X] (hL : puigSubgroup X ≤ Y) :
    (puigLower Y).map Y.subtype = puigLower X := by
  have h := map_puigSubgroup_eq_puigSubgroup hL
  refine le_antisymm ?_ ?_
  · have h1 := map_puigLambda_le_puigLambda_of_le (Y := Y) (V := puigSubgroup Y) h.ge
    rwa [puigLambda_puigSubgroup, puigLambda_puigSubgroup] at h1
  · have hY : puigLambda (puigSubgroup X) ≤ Y :=
      calc puigLambda (puigSubgroup X) = puigLower X := puigLambda_puigSubgroup X
        _ ≤ puigUpper X := puigLower_le_puigUpper
        _ = puigSubgroup X := puigSubgroup_eq_puigUpper.symm
        _ ≤ Y := hL
    have h1 := puigLambda_le_map_puigLambda (Y := Y) (V := puigSubgroup Y) h.le hY
    rwa [puigLambda_puigSubgroup, puigLambda_puigSubgroup] at h1

theorem map_puigCenter_eq_puigCenter {Y : Subgroup X} [Finite X] (hL : puigSubgroup X ≤ Y) :
    (puigCenter Y).map Y.subtype = puigCenter X := by
  have h := map_puigSubgroup_eq_puigSubgroup hL
  ext x
  simp only [puigCenter_eq_inf_centralizer, mem_map, mem_inf, mem_centralizer_iff, coe_subtype,
    Subtype.exists]
  constructor
  · rintro ⟨y, hy, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨h ▸ mem_map_of_mem _ hy1, fun g hg => ?_⟩
    have hgY : g ∈ Y := hL hg
    have hmem : (⟨g, hgY⟩ : Y) ∈ puigSubgroup Y :=
      (mem_puigSubgroup_iff_of_puigSubgroup_le hL ⟨g, hgY⟩).2 hg
    exact congrArg Subtype.val (hy2 _ hmem)
  · rintro ⟨hx1, hx2⟩
    have hxY : x ∈ Y := hL hx1
    refine ⟨x, hxY, ⟨(mem_puigSubgroup_iff_of_puigSubgroup_le hL ⟨x, hxY⟩).2 hx1, ?_⟩, rfl⟩
    intro g hg
    exact Subtype.ext (hx2 _ (h ▸ mem_map_of_mem _ hg))

end CFSG.FeitThompson

end
