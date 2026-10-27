module

public import CFSG.GH74.GLS.C3.Layer2.LocalBasic
public import CFSG.GH74.GLS.C3.Prop121.ModelFiveBase

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem isSylow_T5
    : ∃ P : Sylow 2 (Fgrp 5), (P : Subgroup (Fgrp 5)).map (Fgrp 5).subtype = T5 := by
  have hcardF : (Nat.card (Fgrp 5)).factorization 2 = 5 := by
    rw [card_Fgrp_eq, Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have hcard : Nat.card (T5.subgroupOf (Fgrp 5)) = 2 ^ (Nat.card (Fgrp 5)).factorization 2 := by
    rw [hcardF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe T5_le_Fgrp).toEquiv, card_T5]
    norm_num
  refine ⟨Sylow.ofCard _ hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  exact Subgroup.map_subgroupOf_eq_of_le T5_le_Fgrp

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem exists_equiv_T5 (h : IsAConfig 5 x K T Q S a)
    (ι₀ : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp 5))
    (hι₀1 : ((ι₀ (xC x) : Fgrp 5) : Amb 5) = x0 5)
    (hι₀Q : ∀ c : ↥(centralizer ({x} : Set G)), (((ι₀ c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ Q)) :
    ∃ ι : ↥(centralizer ({x} : Set G)) ≃* ↥(Fgrp 5), ((ι (xC x) : Fgrp 5) : Amb 5) = x0 5 ∧
      (∀ c : ↥(centralizer ({x} : Set G)), (((ι c : Fgrp 5) : Amb 5).1 = 1 ↔ (c : G) ∈ Q)) ∧
      (∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ T ↔ ((ι c : Fgrp 5) : Amb 5) ∈ T5) := by
  obtain ⟨P0, hP0⟩ := isSylow_T5
  obtain ⟨hTle, hTp, hTidx⟩ := isSylowOf_iff.1 h.sylowT
  have hTm : IsSylowOf 2
      ((T.subgroupOf (centralizer ({x} : Set G))).map ι₀.toMonoidHom) (⊤ : Subgroup (Fgrp 5)) := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hTp.comap_subtype.map _, ?_⟩
    rw [Subgroup.relIndex_top_right,
      Subgroup.index_map_of_bijective (f := ι₀.toMonoidHom) ι₀.bijective]
    exact hTidx
  have hP0' : IsSylowOf 2 (P0 : Subgroup (Fgrp 5)) ⊤ :=
    isSylowOf_iff.2 ⟨le_top, P0.isPGroup', by
      rw [Subgroup.relIndex_top_right]; exact P0.not_dvd_index⟩
  obtain ⟨g, -, hg⟩ := hTm.exists_mem_conj hP0'
  have hP0mem : ∀ y : Fgrp 5, y ∈ (P0 : Subgroup (Fgrp 5)) ↔ ((y : Fgrp 5) : Amb 5) ∈ T5 := by
    intro y
    rw [← hP0]
    exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm
  refine ⟨ι₀.trans (MulAut.conj g), ?_, fun c => ?_, fun c => ?_⟩
  · have hcen := x0_central_aux 5 g.2
    show ((g * ι₀ (xC x) * g⁻¹ : Fgrp 5) : Amb 5) = x0 5
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hι₀1, hcen, mul_inv_cancel_right]
  · rw [← hι₀Q c]
    show ((g * ι₀ c * g⁻¹ : Fgrp 5) : Amb 5).1 = 1 ↔ _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv]
    exact conj_eq_one_iff
  · show (c : G) ∈ T ↔ ((g * ι₀ c * g⁻¹ : Fgrp 5) : Amb 5) ∈ T5
    rw [← hP0mem, hg]
    have : g⁻¹ * (g * ι₀ c * g⁻¹) * g = ι₀ c := by group
    rw [this, Subgroup.mem_map_equiv]
    simp [Subgroup.mem_subgroupOf]

end CFSG.GH74.GLS.C3.Prop121
