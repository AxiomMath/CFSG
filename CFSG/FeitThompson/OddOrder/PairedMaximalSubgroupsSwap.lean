module

public import CFSG.FeitThompson.Definitions.LocalTypesIIThroughV
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G]

theorem cyclicTIset_comm (W₁ W₂ : Subgroup G) : cyclicTIset W₂ W₁ = cyclicTIset W₁ W₂ := by
  have h : W₂ ⊔ W₁ = W₁ ⊔ W₂ := sup_comm ..
  ext x
  rw [mem_cyclicTIset, mem_cyclicTIset, h]
  tauto

variable [Finite G] {S T W₁ W₂ : Subgroup G}

structure IsTypePPair (S T W₁ W₂ : Subgroup G) : Prop where
  odd_natCard : Odd (Nat.card G)
  isSimpleGroup : IsSimpleGroup G
  not_isMulCommutative : ¬ IsMulCommutative G
  isSolvable : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K
  isCoatom_left : IsCoatom S
  isCoatom_right : IsCoatom T
  ne : S ≠ T
  ne_bot_left : W₁ ≠ ⊥
  ne_bot_right : W₂ ≠ ⊥
  isCyclic_left : IsCyclic W₁
  isCyclic_right : IsCyclic W₂
  isInternalDirectProduct : IsInternalDirectProduct (W₁ ⊔ W₂) W₁ W₂
  isCyclic_sup : IsCyclic (W₁ ⊔ W₂ : Subgroup G)
  sup_commutator_left : ⁅S, S⁆ ⊔ W₁ = S
  disjoint_commutator_left : Disjoint (⁅S, S⁆ : Subgroup G) W₁
  sup_commutator_right : ⁅T, T⁆ ⊔ W₂ = T
  disjoint_commutator_right : Disjoint (⁅T, T⁆ : Subgroup G) W₂
  inf_eq : S ⊓ T = W₁ ⊔ W₂
  isTIWithNormalizer : IsTIWithNormalizer (cyclicTIset W₁ W₂) (W₁ ⊔ W₂)
  typeIIToV_left : IsTypeII S ∨ IsTypeIII S ∨ IsTypeIV S ∨ IsTypeV S
  typeIIToV_right : IsTypeII T ∨ IsTypeIII T ∨ IsTypeIV T ∨ IsTypeV T
  typeII : IsTypeII S ∨ IsTypeII T
  conj_of_not_isTypeI : ∀ M : Subgroup G, IsCoatom M → ¬ IsTypeI M →
    (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = T)

theorem IsTypePPair.symm (h : IsTypePPair S T W₁ W₂) : IsTypePPair T S W₂ W₁ := by
  have hsup : W₂ ⊔ W₁ = W₁ ⊔ W₂ := sup_comm ..
  exact
  { odd_natCard := h.odd_natCard
    isSimpleGroup := h.isSimpleGroup
    not_isMulCommutative := h.not_isMulCommutative
    isSolvable := h.isSolvable
    isCoatom_left := h.isCoatom_right
    isCoatom_right := h.isCoatom_left
    ne := h.ne.symm
    ne_bot_left := h.ne_bot_right
    ne_bot_right := h.ne_bot_left
    isCyclic_left := h.isCyclic_right
    isCyclic_right := h.isCyclic_left
    isInternalDirectProduct := hsup ▸ h.isInternalDirectProduct.symm
    isCyclic_sup := hsup ▸ h.isCyclic_sup
    sup_commutator_left := h.sup_commutator_right
    disjoint_commutator_left := h.disjoint_commutator_right
    sup_commutator_right := h.sup_commutator_left
    disjoint_commutator_right := h.disjoint_commutator_left
    inf_eq := by rw [inf_comm, h.inf_eq, hsup]
    isTIWithNormalizer := by rw [cyclicTIset_comm, hsup]; exact h.isTIWithNormalizer
    typeIIToV_left := h.typeIIToV_right
    typeIIToV_right := h.typeIIToV_left
    typeII := h.typeII.symm
    conj_of_not_isTypeI := fun M hM hI => (h.conj_of_not_isTypeI M hM hI).symm }

namespace IsTypePPair

variable (h : IsTypePPair S T W₁ W₂)

include h

theorem ne_top_left : S ≠ ⊤ := h.isCoatom_left.1

theorem ne_top_right : T ≠ ⊤ := h.isCoatom_right.1

theorem lt_top_left : S < ⊤ := lt_top_iff_ne_top.2 h.ne_top_left

theorem lt_top_right : T < ⊤ := lt_top_iff_ne_top.2 h.ne_top_right

theorem le_left_W₁ : W₁ ≤ S := h.sup_commutator_left ▸ le_sup_right

theorem le_right_W₂ : W₂ ≤ T := h.sup_commutator_right ▸ le_sup_right

theorem sup_le_left : W₁ ⊔ W₂ ≤ S := h.inf_eq ▸ inf_le_left

theorem sup_le_right : W₁ ⊔ W₂ ≤ T := h.inf_eq ▸ inf_le_right

theorem le_left_W₂ : W₂ ≤ S := le_sup_right.trans h.sup_le_left

theorem le_right_W₁ : W₁ ≤ T := le_sup_left.trans h.sup_le_right

theorem disjoint_W₁_W₂ : Disjoint W₁ W₂ := h.isInternalDirectProduct.disjoint

theorem inf_W₁_W₂ : W₁ ⊓ W₂ = ⊥ := h.isInternalDirectProduct.inf_eq_bot

theorem commute_W₁_W₂ {x y : G} (hx : x ∈ W₁) (hy : y ∈ W₂) : Commute x y :=
  h.isInternalDirectProduct.commute hx hy

theorem coe_sup_eq_mul : ((W₁ ⊔ W₂ : Subgroup G) : Set G) = (W₁ : Set G) * (W₂ : Set G) :=
  h.isInternalDirectProduct.coe_eq_mul

theorem natCard_sup : Nat.card (W₁ ⊔ W₂ : Subgroup G) = Nat.card W₁ * Nat.card W₂ :=
  h.isInternalDirectProduct.card_eq_mul

theorem normalizer_cyclicTIset : normalizer (cyclicTIset W₁ W₂) = W₁ ⊔ W₂ :=
  h.isTIWithNormalizer.normalizer_eq

theorem isComplement'_subgroupOf_commutator_left :
    ((⁅S, S⁆ : Subgroup G).subgroupOf S).IsComplement' (W₁.subgroupOf S) := by
  have := normal_subgroupOf_commutator_self S
  refine (isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_).symm
  · rw [← Subgroup.subgroupOf_sup (Subgroup.commutator_le_self S) h.le_left_W₁,
      h.sup_commutator_left, Subgroup.subgroupOf_self]
  · rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
      disjoint_iff.1 h.disjoint_commutator_left]
    simp

theorem isComplement'_subgroupOf_commutator_right :
    ((⁅T, T⁆ : Subgroup G).subgroupOf T).IsComplement' (W₂.subgroupOf T) :=
  h.symm.isComplement'_subgroupOf_commutator_left

theorem natCard_left : Nat.card S = Nat.card (⁅S, S⁆ : Subgroup G) * Nat.card W₁ := by
  have hc := h.isComplement'_subgroupOf_commutator_left.card_mul_card
  rwa [natCard_subgroupOf (Subgroup.commutator_le_self S), natCard_subgroupOf h.le_left_W₁,
    eq_comm] at hc

theorem natCard_right : Nat.card T = Nat.card (⁅T, T⁆ : Subgroup G) * Nat.card W₂ :=
  h.symm.natCard_left

end IsTypePPair

end

end CFSG.FeitThompson
