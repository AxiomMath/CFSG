module

public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Prime.Defs

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {E : Type*} [Group E] {A B U : Subgroup E}

theorem coe_mul_coe_inf_eq_coe_of_isComplement' (h : A.IsComplement' B) (hAU : A ≤ U) :
    (A : Set E) * ((U ⊓ B : Subgroup E) : Set E) = (U : Set E) := by
  ext u
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact U.mul_mem (hAU ha) (Subgroup.mem_inf.1 hb).1
  · intro hu
    obtain ⟨⟨a, b⟩, hab, -⟩ := h.existsUnique u
    have hbU : (b : E) ∈ U := by
      have hb : (b : E) = (a : E)⁻¹ * u := by rw [← hab]; group
      rw [hb]
      exact U.mul_mem (U.inv_mem (hAU a.2)) hu
    exact Set.mem_mul.2 ⟨a, a.2, b, Subgroup.mem_inf.2 ⟨hbU, b.2⟩, hab⟩

theorem inf_inf_eq_bot_of_isComplement' (h : A.IsComplement' B) (U : Subgroup E) :
    A ⊓ (U ⊓ B) = ⊥ :=
  le_bot_iff.1 fun x hx => Subgroup.disjoint_def.1 h.disjoint (x := x) (Subgroup.mem_inf.1 hx).1
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).2).2

theorem isComplement'_subgroupOf_of_isComplement' (h : A.IsComplement' B) (hAU : A ≤ U) :
    (A.subgroupOf U).IsComplement' ((U ⊓ B).subgroupOf U) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · refine Subgroup.disjoint_def.2 fun {x} hx hx' => Subtype.ext ?_
    rw [Subgroup.mem_subgroupOf] at hx hx'
    have hmem : (x : E) ∈ A ⊓ (U ⊓ B) := Subgroup.mem_inf.2 ⟨hx, hx'⟩
    rw [inf_inf_eq_bot_of_isComplement' h U] at hmem
    simpa using hmem
  · refine Set.eq_univ_of_forall fun x => ?_
    have hx : (x : E) ∈ (A : Set E) * ((U ⊓ B : Subgroup E) : Set E) := by
      rw [coe_mul_coe_inf_eq_coe_of_isComplement' h hAU]; exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨⟨a, hAU ha⟩, Subgroup.mem_subgroupOf.2 ha,
      ⟨b, (Subgroup.mem_inf.1 hb).1⟩, Subgroup.mem_subgroupOf.2 hb, Subtype.ext hab⟩

noncomputable def semidirectProductMulEquivOfIsComplement' [A.Normal] (h : A.IsComplement' B)
    (hAU : A ≤ U) :
    letI : (A.subgroupOf U).Normal := ‹A.Normal›.subgroupOf U
    (A.subgroupOf U) ⋊[((A.subgroupOf U).normalizerMonoidHom).comp
      (Subgroup.inclusion ((A.subgroupOf U).normalizer_eq_top ▸ le_top))]
      ((U ⊓ B).subgroupOf U) ≃* U :=
  letI : (A.subgroupOf U).Normal := ‹A.Normal›.subgroupOf U
  SemidirectProduct.mulEquivSubgroup (isComplement'_subgroupOf_of_isComplement' h hAU)

@[simp]
theorem semidirectProductMulEquivOfIsComplement'_apply [A.Normal] (h : A.IsComplement' B)
    (hAU : A ≤ U)
    (x : letI : (A.subgroupOf U).Normal := ‹A.Normal›.subgroupOf U
      (A.subgroupOf U) ⋊[((A.subgroupOf U).normalizerMonoidHom).comp
        (Subgroup.inclusion ((A.subgroupOf U).normalizer_eq_top ▸ le_top))]
        ((U ⊓ B).subgroupOf U)) :
    (semidirectProductMulEquivOfIsComplement' h hAU x : U) = (x.left : U) * (x.right : U) :=
  SemidirectProduct.mulEquivSubgroup_apply _ x

theorem natCard_mul_natCard_inf_of_isComplement' (h : A.IsComplement' B) (hAU : A ≤ U) :
    Nat.card A * Nat.card (U ⊓ B : Subgroup E) = Nat.card U := by
  have h2 := natCard_mul_mul_natCard_inf A (U ⊓ B)
  rw [inf_inf_eq_bot_of_isComplement' h U, Subgroup.card_bot, mul_one,
    coe_mul_coe_inf_eq_coe_of_isComplement' h hAU] at h2
  simpa using h2.symm

theorem index_mul_natCard_inf_of_isComplement' [Finite E] (h : A.IsComplement' B) (hAU : A ≤ U) :
    U.index * Nat.card (U ⊓ B : Subgroup E) = Nat.card B := by
  have h1 := natCard_mul_natCard_inf_of_isComplement' h hAU
  have h2 : U.index * Nat.card U = Nat.card E := U.index_mul_card
  have h3 : Nat.card A * Nat.card B = Nat.card E := h.card_mul_card
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A)) ?_
  calc Nat.card A * (U.index * Nat.card (U ⊓ B : Subgroup E))
      = U.index * (Nat.card A * Nat.card (U ⊓ B : Subgroup E)) := by ring
    _ = Nat.card E := by rw [h1, h2]
    _ = Nat.card A * Nat.card B := h3.symm

theorem relIndex_inf_eq_index_of_isComplement' [Finite E] (h : A.IsComplement' B) (hAU : A ≤ U) :
    (U ⊓ B).relIndex B = U.index := by
  have hb : Nat.card ((U ⊓ B).subgroupOf B) = Nat.card (U ⊓ B : Subgroup E) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : U ⊓ B ≤ B)).toEquiv
  have h4 : (U ⊓ B).relIndex B * Nat.card (U ⊓ B : Subgroup E) = Nat.card B := by
    rw [Subgroup.relIndex, ← hb]
    exact Subgroup.index_mul_card _
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (U ⊓ B : Subgroup E)))
    (h4.trans (index_mul_natCard_inf_of_isComplement' h hAU).symm)

theorem pow_dvd_natCard_inf_of_not_dvd_index [Finite E] {p n : ℕ} (hp : p.Prime)
    (h : A.IsComplement' B) (hAU : A ≤ U) (hpU : ¬ p ∣ U.index) (hpB : p ^ n ∣ Nat.card B) :
    p ^ n ∣ Nat.card (U ⊓ B : Subgroup E) := by
  rw [← index_mul_natCard_inf_of_isComplement' h hAU] at hpB
  exact (Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.2 hpU)).dvd_of_dvd_mul_left hpB

theorem dvd_natCard_inf_of_not_dvd_index [Finite E] {p : ℕ} (hp : p.Prime)
    (h : A.IsComplement' B) (hAU : A ≤ U) (hpU : ¬ p ∣ U.index) (hpB : p ∣ Nat.card B) :
    p ∣ Nat.card (U ⊓ B : Subgroup E) := by
  simpa using pow_dvd_natCard_inf_of_not_dvd_index (n := 1) hp h hAU hpU (by simpa using hpB)

end

end CFSG.FeitThompson
