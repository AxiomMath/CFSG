module

public import CFSG.FeitThompson.OddOrder.PartnerKernelPrimeOverlapCover
public import CFSG.FeitThompson.Local.TwoCoreMixedSaturationMeasure

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

variable {G : Type*} [Group G]

namespace IsFrobeniusPartnerConfig

variable {N H U K W1 W2 : Subgroup G} (hc : IsFrobeniusPartnerConfig N H U K W1 W2)

include hc

theorem cyclicTIDiff_eq_coe_sdiff_union :
    cyclicTIDiff (W1 ⊔ W2) W1 W2
      = ((W1 ⊔ W2 : Subgroup G) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) := by
  rw [hc.cyclicTIDiff_eq, hc.coe_sup_W1_W2_eq]

section Finite

variable [Finite G]

theorem natCard_K_eq : Nat.card K = Nat.card H * Nat.card U :=
  natCard_of_coe_eq_mul hc.coe_K_eq hc.disjoint_H_U.eq_bot

theorem natCard_N_eq : Nat.card N = Nat.card H * Nat.card U * Nat.card W2 := by
  rw [natCard_of_coe_eq_mul hc.coe_N_eq hc.disjoint_K_W2.eq_bot, hc.natCard_K_eq]

theorem natCard_sup_W1_W2_eq : Nat.card (W1 ⊔ W2 : Subgroup G) = Nat.card W1 * Nat.card W2 :=
  natCard_of_coe_eq_mul hc.coe_sup_W1_W2_eq hc.inf_W1_W2_eq_bot

theorem ncard_cyclicTIDiff_eq :
    ((cyclicTIDiff (W1 ⊔ W2) W1 W2).ncard : ℝ)
      = ((Nat.card W1 : ℝ) - 1) * ((Nat.card W2 : ℝ) - 1) := by
  rw [hc.cyclicTIDiff_eq_coe_sdiff_union,
    ncard_sdiff_union_eq hc.coe_sup_W1_W2_eq hc.inf_W1_W2_eq_bot]

theorem measure_conjugatesOfSet_H_lt :
    ((Group.conjugatesOfSet ((H : Set G) \ {1})).ncard : ℝ) / Nat.card G
      < 1 / (Nat.card U * Nat.card W2) :=
  measure_conjugatesOfSet_punctured_lt (P := H) (S := N) Nat.card_pos Nat.card_pos hc.le_N_H
    hc.normal_subgroupOf_H hc.natCard_N_eq

theorem measure_conjugatesOfSet_cyclicTIDiff_eq
    (hND : {g : G | (fun x => g⁻¹ * x * g) '' cyclicTIDiff (W1 ⊔ W2) W1 W2
        = cyclicTIDiff (W1 ⊔ W2) W1 W2} = ((W1 ⊔ W2 : Subgroup G) : Set G))
    (hTI : ∀ g ∉ (W1 ⊔ W2 : Subgroup G), cyclicTIDiff (W1 ⊔ W2) W1 W2 ∩
      ((fun x => g⁻¹ * x * g) '' cyclicTIDiff (W1 ⊔ W2) W1 W2) = ∅) :
    ((Group.conjugatesOfSet (cyclicTIDiff (W1 ⊔ W2) W1 W2)).ncard : ℝ) / Nat.card G
      = ((Nat.card W1 : ℝ) - 1) * ((Nat.card W2 : ℝ) - 1)
          / (Nat.card W1 * Nat.card W2) := by
  have hND' : Subgroup.normalizer (cyclicTIDiff (W1 ⊔ W2) W1 W2) = W1 ⊔ W2 :=
    SetLike.coe_injective ((setOf_conj_eq_self_eq_normalizer _).symm.trans hND)
  have hV := hc.cyclicTIDiff_eq_coe_sdiff_union
  have he : 1 < Nat.card W1 := (Subgroup.one_lt_card_iff_ne_bot W1).2 hc.ne_bot_W1
  have hp : 1 < Nat.card W2 := (Subgroup.one_lt_card_iff_ne_bot W2).2 hc.ne_bot_W2
  have h3 := measure_conjugatesOfSet_mixed_eq (G := G) (W := W1 ⊔ W2) (W₁ := W1) (W₂ := W2)
    (q := Nat.card W1) (p := Nat.card W2) he hp rfl rfl hc.coe_sup_W1_W2_eq hc.inf_W1_W2_eq_bot
    (by rw [← hV]; exact hND') (by intro g hg; rw [← hV]; exact hTI g hg)
  rw [← hV] at h3
  rw [h3]
  ring

theorem measure_le_of_subset_gcd_orderOf {e p u : ℕ}
    (he : Nat.card W1 = e) (hp : Nat.card W2 = p) (hu : Nat.card U = u)
    (hND : {g : G | (fun x => g⁻¹ * x * g) '' cyclicTIDiff (W1 ⊔ W2) W1 W2
        = cyclicTIDiff (W1 ⊔ W2) W1 W2} = ((W1 ⊔ W2 : Subgroup G) : Set G))
    (hTI : ∀ g ∉ (W1 ⊔ W2 : Subgroup G), cyclicTIDiff (W1 ⊔ W2) W1 W2 ∩
      ((fun x => g⁻¹ * x * g) '' cyclicTIDiff (W1 ⊔ W2) W1 W2) = ∅)
    {B : Set G} (hB : B ⊆ {g : G | 1 < Nat.gcd (orderOf g) e}) :
    (B.ncard : ℝ) / Nat.card G
      ≤ 1 / ((u : ℝ) * p) + ((e : ℝ) - 1) * ((p : ℝ) - 1) / ((e : ℝ) * p) := by
  subst he hp hu
  have h1 := hc.measure_conjugatesOfSet_H_lt
  have h3 := hc.measure_conjugatesOfSet_cyclicTIDiff_eq hND hTI
  have hcover : B ⊆ Group.conjugatesOfSet ((H : Set G) \ {1})
      ∪ Group.conjugatesOfSet (cyclicTIDiff (W1 ⊔ W2) W1 W2) :=
    fun g hg => hc.mem_union_conjugatesOfSet (hB hg)
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have hle : (B.ncard : ℝ) ≤ ((Group.conjugatesOfSet ((H : Set G) \ {1})
      ∪ Group.conjugatesOfSet (cyclicTIDiff (W1 ⊔ W2) W1 W2)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hcover (Set.toFinite _)
  have hmono : (B.ncard : ℝ) / Nat.card G
      ≤ ((Group.conjugatesOfSet ((H : Set G) \ {1})
      ∪ Group.conjugatesOfSet (cyclicTIDiff (W1 ⊔ W2) W1 W2)).ncard : ℝ) / Nat.card G :=
    div_le_div_of_nonneg_right hle hG.le
  have h4 := measure_union_le (G := G) (Group.conjugatesOfSet ((H : Set G) \ {1}))
    (Group.conjugatesOfSet (cyclicTIDiff (W1 ⊔ W2) W1 W2))
  linarith

end Finite

end IsFrobeniusPartnerConfig

end CFSG.FeitThompson
