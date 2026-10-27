module

public import CFSG.ClassicalInvolution.Q3.Q3TIRed
public import CFSG.ClassicalInvolution.Q3.M11Kernel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification

theorem le_sup_centralizer_of_centralizer_ne_bot {Y : Type} [Group Y] [Finite Y]
    (hBelow : CIT3Below (Nat.card Y)) (hO : classicalInvolutionOddCore Y = ⊥) {z : Y}
    {L : Subgroup Y} (hz : IsClassicalMember3 L z) {T : Subgroup Y} [T.Normal]
    (hT : IsComponentOf T ⊤) (hTL : T ⊔ L = ⊤) (hgen : Subgroup.normalClosure (L : Set Y) = ⊤)
    (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set Y))
    (hD : Subgroup.centralizer (T : Set Y) ≠ ⊥) : L ≤ T ⊔ Subgroup.centralizer (T : Set Y) := by
  set D := Subgroup.centralizer (T : Set Y) with hDdef
  set π := QuotientGroup.mk' D with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hL' := isClassicalMember3_map_centralizer hO hz hT hTL hTz
  have hT' := isComponentOf_map_centralizer hT
  have hC' := centralizer_map_eq_bot hO hz hT hTL hTz
  have hO' := oddCore_quotient_centralizer_eq_bot hO hz hT hTL hTz
  have hgen' : Subgroup.normalClosure ((L.map π : Subgroup (Y ⧸ D)) : Set (Y ⧸ D)) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ π hπs, hgen,
      Subgroup.map_top_of_surjective _ hπs]
  have hΛ := Q3B.inClass3_conjClass hL' hgen'
  have hcard : Nat.card (Y ⧸ D) < Nat.card Y := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D]
    have h1 : 1 < Nat.card D := (Subgroup.one_lt_card_iff_ne_bot D).mpr hD
    have h0 : 0 < Nat.card (Y ⧸ D) := Nat.card_pos
    nlinarith
  have hLie := hBelow (Y ⧸ D) hcard _ hΛ
  have hTO : T.map π ⊓ classicalInvolutionOddCore (Y ⧸ D) = ⊥ := by rw [hO', inf_bot_eq]
  have h := le_sup_centralizer_of_lieSystemMod3 m11Facts hLie (Q3B.mem_conjClass_self _) hT' hTO
  rw [hC', sup_bot_eq] at h
  intro l hl
  obtain ⟨t, ht, htl⟩ := h (Subgroup.mem_map_of_mem π hl)
  have h1 : π (t⁻¹ * l) = 1 := by rw [map_mul, map_inv, htl, inv_mul_cancel]
  have hk : t⁻¹ * l ∈ D := (QuotientGroup.eq_one_iff _).mp h1
  have : l = t * (t⁻¹ * l) := by group
  rw [this]
  exact Subgroup.mul_mem_sup ht hk

end CFSG.ClassicalInvolution.Q3.Q3T
