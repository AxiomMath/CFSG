module

public import CFSG.FeitThompson.OddOrder.PairOrientationByFactorOrder
import CFSG.FeitThompson.OddOrder.PConfigComplementCentralizer
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G]

variable [Finite G] {S T E D W₁ W₂ : Subgroup G}

namespace IsTypePPair

variable (hp : IsTypePPair S T W₁ W₂)

include hp

theorem index_subgroupOf_commutator : ((⁅S, S⁆ : Subgroup G).subgroupOf S).index = Nat.card W₁ := by
  have h := hp.isComplement'_subgroupOf_commutator_left.symm.index_eq_card
  rwa [natCard_subgroupOf hp.le_left_W₁] at h

theorem le_commutator_W₂ : W₂ ≤ ⁅S, S⁆ := by
  have := normal_subgroupOf_commutator_self S
  have hcop : (Nat.card (W₂.subgroupOf S)).Coprime ((⁅S, S⁆ : Subgroup G).subgroupOf S).index := by
    rw [hp.index_subgroupOf_commutator, natCard_subgroupOf hp.le_left_W₂]
    exact hp.coprime_natCard.symm
  have hle := le_of_coprime_natCard_index hcop
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (hle (Subgroup.mem_subgroupOf.2 hx :
    (⟨x, hp.le_left_W₂ hx⟩ : S) ∈ W₂.subgroupOf S))

theorem centralizer_sup_le : centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G) ≤ W₁ ⊔ W₂ := by
  have hset : cyclicTIset W₁ W₂
      = ((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)) := by
    ext x; simp [mem_cyclicTIset]
  refine centralizer_le_of_normalizer_sdiff_union_eq hp.ne_bot_left hp.ne_bot_right
    hp.isInternalDirectProduct.coe_eq_mul hp.isInternalDirectProduct.inf_eq_bot
    (fun x hx y hy => hp.isInternalDirectProduct.commute hx hy) ?_
  rw [← hset]
  exact hp.isTIWithNormalizer.normalizer_eq

theorem inf_commutator_sup_eq_W₂ : (⁅S, S⁆ : Subgroup G) ⊓ (W₁ ⊔ W₂) = W₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf hp.le_commutator_W₂ le_sup_right)
  obtain ⟨hxS, hxW⟩ := Subgroup.mem_inf.1 hx
  rw [← SetLike.mem_coe, hp.isInternalDirectProduct.coe_eq_mul] at hxW
  obtain ⟨a, ha, b, hb, rfl⟩ := hxW
  have hbS : b ∈ (⁅S, S⁆ : Subgroup G) := hp.le_commutator_W₂ hb
  have haS : a ∈ (⁅S, S⁆ : Subgroup G) := by
    have hrw : a = a * b * b⁻¹ := by group
    rw [hrw]
    exact mul_mem hxS (inv_mem hbS)
  have ha1 : a = 1 := by
    have hmem : a ∈ (⁅S, S⁆ : Subgroup G) ⊓ W₁ := Subgroup.mem_inf.2 ⟨haS, ha⟩
    rw [disjoint_iff.1 hp.disjoint_commutator_left] at hmem
    simpa using hmem
  simpa [ha1] using hb

end IsTypePPair

theorem IsTypePPair.eq_W₂_of_isWitnessedPConfiguration (hp : IsTypePPair S T W₁ W₂)
    (hc : IsWitnessedPConfiguration S E W₁ D) : D = W₂ := by
  have hDcomm : D = (⁅S, S⁆ : Subgroup G) ⊓ centralizer (W₁ : Set G) :=
    hc.inf_centralizer_W₁_eq_W₂.symm
  have hW₂D : W₂ ≤ D := by
    rw [hDcomm]
    exact le_inf hp.le_commutator_W₂ fun x hx => mem_centralizer_iff.2 fun y hy =>
      (hp.isInternalDirectProduct.commute hy hx).eq
  have := hc.isCyclic_W₂
  have hDW : D ≤ W₁ ⊔ W₂ := by
    refine le_trans (fun x hx => ?_) hp.centralizer_sup_le
    refine mem_centralizer_iff.2 fun y hy => ?_
    rw [SetLike.mem_coe, ← SetLike.mem_coe, hp.isInternalDirectProduct.coe_eq_mul] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    have h1 : a * x = x * a :=
      mem_centralizer_iff.1 (hDcomm ▸ hx : x ∈ _ ⊓ centralizer (W₁ : Set G)).2 a ha
    have h2 : b * x = x * b := setLike_mul_comm (hW₂D hb) hx
    calc a * b * x = a * (b * x) := by group
      _ = a * (x * b) := by rw [h2]
      _ = a * x * b := by group
      _ = x * a * b := by rw [h1]
      _ = x * (a * b) := by group
  refine le_antisymm ?_ hW₂D
  rw [← hp.inf_commutator_sup_eq_W₂]
  exact le_inf (hDcomm ▸ inf_le_left) hDW

theorem IsTypePPair.eq_W₂_of_isWitnessedPConfiguration_of_oddOrder_of_proper_solvable
    [IsSimpleGroup G] (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hp : IsTypePPair S T W₁ W₂) (hc : IsWitnessedPConfiguration S E W₁ D) : D = W₂ :=
  hp.eq_W₂_of_isWitnessedPConfiguration hc

theorem IsTypePPair.isWitnessedPConfiguration_W₂ (hp : IsTypePPair S T W₁ W₂)
    (hc : IsWitnessedPConfiguration S E W₁ D) : IsWitnessedPConfiguration S E W₁ W₂ :=
  hp.eq_W₂_of_isWitnessedPConfiguration hc ▸ hc

end

end CFSG.FeitThompson
