module

import CFSG.FeitThompson.OddOrder.NilpotentProperSubgroupNormalClosure
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Nilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {M : Type*} [Group M] {H A U C : Subgroup M}

theorem subtype_image_setOf_conj (hC : C ≤ H) :
    H.subtype '' {x : H | ∃ h : H, ∃ d ∈ C.subgroupOf H, x = h⁻¹ * d * h}
      = {x : M | ∃ h ∈ H, ∃ c ∈ C, x = h⁻¹ * c * h} := by
  ext x
  constructor
  · rintro ⟨y, ⟨h, d, hd, rfl⟩, rfl⟩
    exact ⟨h, h.2, d, mem_subgroupOf.1 hd, by simp⟩
  · rintro ⟨h, hh, c, hc, rfl⟩
    refine ⟨(⟨h, hh⟩ : H)⁻¹ * ⟨c, hC hc⟩ * ⟨h, hh⟩, ⟨⟨h, hh⟩, ⟨c, hC hc⟩, ?_, rfl⟩, by simp⟩
    exact mem_subgroupOf.2 hc

theorem closure_setOf_conj_lt_of_not_le [Finite M] [Group.IsNilpotent H] (hC : C ≤ H)
    (hHC : ¬ H ≤ C) :
    Subgroup.closure {x : M | ∃ h ∈ H, ∃ c ∈ C, x = h⁻¹ * c * h} < H := by
  have h2 : C.subgroupOf H < ⊤ := lt_top_iff_ne_top.2 fun hh => hHC (subgroupOf_eq_top.1 hh)
  calc Subgroup.closure {x : M | ∃ h ∈ H, ∃ c ∈ C, x = h⁻¹ * c * h}
      = (Subgroup.closure {x : H | ∃ h : H, ∃ d ∈ C.subgroupOf H, x = h⁻¹ * d * h}).map
          H.subtype := by rw [MonoidHom.map_closure, subtype_image_setOf_conj hC]
    _ < (⊤ : Subgroup H).map H.subtype :=
        (map_lt_map_iff_of_injective (subtype_injective H)).2
          (closure_conj_lt_top_of_lt_top h2)
    _ = H := by rw [← MonoidHom.range_eq_map, range_subtype]

theorem le_closure_setOf_conj :
    C ≤ Subgroup.closure {x : M | ∃ h ∈ H, ∃ c ∈ C, x = h⁻¹ * c * h} := by
  intro c hc
  exact subset_closure ⟨1, one_mem H, c, hc, by simp⟩

theorem conj_mem_closure_of_conj_mem {S : Set M} {g : M} (h : ∀ x ∈ S, g⁻¹ * x * g ∈ S)
    {y : M} (hy : y ∈ Subgroup.closure S) : g⁻¹ * y * g ∈ Subgroup.closure S := by
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g⁻¹).toMonoidHom := by
    rw [closure_le]
    intro z hz
    simpa using subset_closure (h z hz)
  simpa using hle hy

theorem exists_mul_of_isComplement' (hHA : H.IsComplement' A) (g : M) :
    ∃ h ∈ H, ∃ a ∈ A, g = h * a := by
  obtain ⟨⟨⟨h, hh⟩, ⟨a, ha⟩⟩, hg⟩ := (isComplement'_def.1 hHA).2 g
  exact ⟨h, hh, a, ha, hg.symm⟩

theorem conj_mem_of_normal_subgroupOf (hUA : U ≤ A) (hUn : (U.subgroupOf A).Normal)
    {a : M} (ha : a ∈ A) {u : M} (hu : u ∈ U) : a⁻¹ * u * a ∈ U := by
  simpa using (normal_subgroupOf_iff hUA).1 hUn u a⁻¹ hu (inv_mem ha)

theorem conj_mem_inf_centralizer [H.Normal] (hUA : U ≤ A) (hUn : (U.subgroupOf A).Normal)
    {a : M} (ha : a ∈ A) {c : M} (hc : c ∈ H ⊓ centralizer (U : Set M)) :
    a⁻¹ * c * a ∈ H ⊓ centralizer (U : Set M) := by
  rw [Subgroup.mem_inf] at hc ⊢
  obtain ⟨hcH, hcC⟩ := hc
  refine ⟨by simpa using ‹H.Normal›.conj_mem c hcH a⁻¹, ?_⟩
  rw [mem_centralizer_iff]
  intro u hu
  have hu' : a * u * a⁻¹ ∈ U := by
    simpa using conj_mem_of_normal_subgroupOf hUA hUn (inv_mem ha) hu
  have hcomm := mem_centralizer_iff.1 hcC _ hu'
  calc u * (a⁻¹ * c * a) = a⁻¹ * ((a * u * a⁻¹) * c) * a := by group
    _ = a⁻¹ * (c * (a * u * a⁻¹)) * a := by rw [hcomm]
    _ = (a⁻¹ * c * a) * u := by group

theorem conj_mem_setOf_conj_of_mem_left {h₀ : M} (hh₀ : h₀ ∈ H) {x : M}
    (hx : x ∈ {x : M | ∃ h ∈ H, ∃ c ∈ C, x = h⁻¹ * c * h}) :
    h₀⁻¹ * x * h₀ ∈ {x : M | ∃ h ∈ H, ∃ c ∈ C, x = h⁻¹ * c * h} := by
  obtain ⟨h, hh, c, hc, rfl⟩ := hx
  exact ⟨h * h₀, mul_mem hh hh₀, c, hc, by group⟩

theorem conj_mem_setOf_conj_of_mem_right [H.Normal] (hUA : U ≤ A)
    (hUn : (U.subgroupOf A).Normal) {a : M} (ha : a ∈ A) {x : M}
    (hx : x ∈ {x : M | ∃ h ∈ H, ∃ c ∈ H ⊓ centralizer (U : Set M), x = h⁻¹ * c * h}) :
    a⁻¹ * x * a ∈ {x : M | ∃ h ∈ H, ∃ c ∈ H ⊓ centralizer (U : Set M), x = h⁻¹ * c * h} := by
  obtain ⟨h, hh, c, hc, rfl⟩ := hx
  refine ⟨a⁻¹ * h * a, by simpa using ‹H.Normal›.conj_mem h hh a⁻¹,
    a⁻¹ * c * a, conj_mem_inf_centralizer hUA hUn ha hc, by group⟩

theorem closure_setOf_conj_normal [H.Normal] (hHA : H.IsComplement' A) (hUA : U ≤ A)
    (hUn : (U.subgroupOf A).Normal) :
    (Subgroup.closure
      {x : M | ∃ h ∈ H, ∃ c ∈ H ⊓ centralizer (U : Set M), x = h⁻¹ * c * h}).Normal := by
  constructor
  intro n hn g
  obtain ⟨h, hh, a, ha, hga⟩ := exists_mul_of_isComplement' hHA g⁻¹
  have hg : g = (h * a)⁻¹ := by rw [← hga, inv_inv]
  have key : ∀ x ∈ {x : M | ∃ h ∈ H, ∃ c ∈ H ⊓ centralizer (U : Set M), x = h⁻¹ * c * h},
      (h * a)⁻¹ * x * (h * a) ∈
        {x : M | ∃ h ∈ H, ∃ c ∈ H ⊓ centralizer (U : Set M), x = h⁻¹ * c * h} := by
    intro x hx
    have hrw : (h * a)⁻¹ * x * (h * a) = a⁻¹ * (h⁻¹ * x * h) * a := by group
    rw [hrw]
    exact conj_mem_setOf_conj_of_mem_right hUA hUn ha (conj_mem_setOf_conj_of_mem_left hh hx)
  rw [hg, inv_inv]
  exact conj_mem_closure_of_conj_mem key hn

theorem not_le_inf_centralizer_of_not_le_centralizer (hUC : ¬ U ≤ centralizer (H : Set M)) :
    ¬ H ≤ H ⊓ centralizer (U : Set M) := fun hle =>
  hUC (le_centralizer_iff.1 (le_inf_iff.1 hle).2)

theorem exists_normal_maximal_centralizer_le [Finite M] [H.Normal] [Group.IsNilpotent H]
    (hHA : H.IsComplement' A) (hUA : U ≤ A) (hUn : (U.subgroupOf A).Normal)
    (hUC : ¬ U ≤ centralizer (H : Set M)) :
    ∃ H₀ : Subgroup M, H₀.Normal ∧ H₀ < H ∧ H ⊓ centralizer (U : Set M) ≤ H₀ ∧
      ∀ K : Subgroup M, K.Normal → H₀ < K → K ≤ H → K = H := by
  have hDlt := closure_setOf_conj_lt_of_not_le (C := H ⊓ centralizer (U : Set M))
    inf_le_left (not_le_inf_centralizer_of_not_le_centralizer hUC)
  have hDn := closure_setOf_conj_normal hHA hUA hUn
  obtain ⟨H₀, hDH₀, hmax⟩ :=
    Finite.exists_le_maximal
      (p := fun K : Subgroup M => K.Normal ∧
        Subgroup.closure {x : M | ∃ h ∈ H, ∃ c ∈ H ⊓ centralizer (U : Set M),
          x = h⁻¹ * c * h} ≤ K ∧ K < H)
      ⟨hDn, le_rfl, hDlt⟩
  obtain ⟨hH₀n, -, hH₀lt⟩ := hmax.prop
  refine ⟨H₀, hH₀n, hH₀lt, le_trans le_closure_setOf_conj hDH₀, ?_⟩
  intro K hKn hlt hKH
  by_contra hne
  exact absurd (hmax.le_of_ge ⟨hKn, le_trans hDH₀ hlt.le, lt_of_le_of_ne hKH hne⟩ hlt.le)
    hlt.not_ge

theorem exists_normal_chiefFactor_centralizer_le [Finite M] [H.Normal] [Group.IsNilpotent H]
    (hHA : H.IsComplement' A) (hUA : U ≤ A) (hUn : (U.subgroupOf A).Normal)
    (hUC : ¬ U ≤ centralizer (H : Set M)) :
    ∃ H₀ : Subgroup M, H₀.Normal ∧ H₀ < H ∧ H ⊓ centralizer (U : Set M) ≤ H₀ ∧
      ∀ K : Subgroup M, K.Normal → H₀ ≤ K → K ≤ H → K = H₀ ∨ K = H := by
  obtain ⟨H₀, hn, hlt, hle, hmax⟩ :=
    exists_normal_maximal_centralizer_le hHA hUA hUn hUC
  refine ⟨H₀, hn, hlt, hle, fun K hKn hH₀K hKH => ?_⟩
  rcases eq_or_lt_of_le hH₀K with h | h
  · exact Or.inl h.symm
  · exact Or.inr (hmax K hKn h hKH)

end

end CFSG.FeitThompson
