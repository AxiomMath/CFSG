module

public import CFSG.FeitThompson.Foundations.FocalGeneratorSet

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)

omit [Fact p.Prime] in
theorem focalSubgroupOf_eq_bot (h : (P : Subgroup G).focalSubgroup = ⊥) :
    (P : Subgroup G).focalSubgroupOf = ⊥ := by
  rw [Subgroup.focalSubgroupOf_def, h, Subgroup.bot_subgroupOf]

variable [Finite G]

theorem index_ker_transferFocal (h : (P : Subgroup G).focalSubgroup = ⊥) :
    (P : Subgroup G).transferFocal.ker.index = Nat.card (P : Subgroup G) := by
  rw [Subgroup.index_eq_card,
    Nat.card_congr (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf P).toEquiv,
    focalSubgroupOf_eq_bot P h]
  exact Nat.card_congr QuotientGroup.quotientBot.toEquiv

theorem ker_transferFocal_isComplement' (h : (P : Subgroup G).focalSubgroup = ⊥) :
    (P : Subgroup G).transferFocal.ker.IsComplement' (P : Subgroup G) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [← index_ker_transferFocal P h]
    exact Subgroup.card_mul_index _
  · rw [disjoint_iff, Subgroup.ker_transferFocal_inf_eq_focalSubgroup, h]

theorem ker_transferFocal_inf_eq_bot (h : (P : Subgroup G).focalSubgroup = ⊥) :
    (P : Subgroup G).transferFocal.ker ⊓ (P : Subgroup G) = ⊥ := by
  rw [Subgroup.ker_transferFocal_inf_eq_focalSubgroup, h]

theorem coe_ker_transferFocal_mul_coe (h : (P : Subgroup G).focalSubgroup = ⊥) :
    ((P : Subgroup G).transferFocal.ker : Set G) * (P : Set G) = Set.univ :=
  Subgroup.IsComplement.mul_eq (ker_transferFocal_isComplement' P h)

theorem ker_transferFocal_sup_eq_top (h : (P : Subgroup G).focalSubgroup = ⊥) :
    (P : Subgroup G).transferFocal.ker ⊔ (P : Subgroup G) = ⊤ :=
  (ker_transferFocal_isComplement' P h).isCompl.sup_eq_top

theorem card_ker_transferFocal (h : (P : Subgroup G).focalSubgroup = ⊥) :
    Nat.card (P : Subgroup G).transferFocal.ker = (P : Subgroup G).index :=
  (ker_transferFocal_isComplement' P h).index_eq_card.symm

theorem coprime_card_ker_transferFocal (h : (P : Subgroup G).focalSubgroup = ⊥) :
    Nat.Coprime (Nat.card (P : Subgroup G).transferFocal.ker) p := by
  rw [card_ker_transferFocal P h]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (Sylow.not_dvd_index P)).symm

theorem exists_normal_pComplement_of_focalSubgroup_eq_bot
    (h : (P : Subgroup G).focalSubgroup = ⊥) :
    ∃ K : Subgroup G, K.Normal ∧ (K : Set G) * (P : Set G) = Set.univ ∧
      K ⊓ (P : Subgroup G) = ⊥ ∧ Nat.card K = (P : Subgroup G).index ∧
      Nat.Coprime (Nat.card K) p :=
  ⟨(P : Subgroup G).transferFocal.ker, inferInstance, coe_ker_transferFocal_mul_coe P h,
    ker_transferFocal_inf_eq_bot P h, card_ker_transferFocal P h,
    coprime_card_ker_transferFocal P h⟩

theorem exists_normal_pComplement_of_focalGeneratorSet_closure_eq_bot
    (h : closure (focalGeneratorSet (P : Subgroup G)) = ⊥) :
    ∃ K : Subgroup G, K.Normal ∧ (K : Set G) * (P : Set G) = Set.univ ∧
      K ⊓ (P : Subgroup G) = ⊥ ∧ Nat.card K = (P : Subgroup G).index ∧
      Nat.Coprime (Nat.card K) p :=
  exists_normal_pComplement_of_focalSubgroup_eq_bot P
    (by rwa [closure_focalGeneratorSet] at h)

end CFSG.FeitThompson
