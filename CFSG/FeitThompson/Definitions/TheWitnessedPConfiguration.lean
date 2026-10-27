module

public import CFSG.FeitThompson.Representations.PrimeTILocalTransporterTISet
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
public import CFSG.FeitThompson.Definitions.NormalSylowHallCore
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G]

theorem le_normalizer_map_subtype_hallCore (M : Subgroup G) :
    M ≤ normalizer (((hallCore M).map M.subtype : Subgroup G) : Set G) := by
  have h : ((hallCore M).map M.subtype).subgroupOf M = hallCore M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hn : (((hallCore M).map M.subtype).subgroupOf M).Normal := by
    rw [h]; exact hallCore_normal
  exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)

theorem normal_subgroupOf_commutator_self (M : Subgroup G) :
    ((⁅M, M⁆ : Subgroup G).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.commutator_le_self M)).2
    (Subgroup.normalizer_commutator_ge_left M M)

theorem commutator_le_normalizer_hallCore (M : Subgroup G) :
    (⁅M, M⁆ : Subgroup G) ≤ normalizer (((hallCore M).map M.subtype : Subgroup G) : Set G) :=
  (Subgroup.commutator_le_self M).trans (le_normalizer_map_subtype_hallCore M)

variable [Finite G]

structure IsWitnessedPConfiguration (M E W₁ W₂ : Subgroup G) : Prop where
  lt_top : M < ⊤
  ne_bot_W₁ : W₁ ≠ ⊥
  isCyclic_W₁ : IsCyclic W₁
  hall_W₁ : (Nat.card W₁).Coprime (W₁.relIndex M)
  sup_commutator_W₁ : ⁅M, M⁆ ⊔ W₁ = M
  disjoint_commutator_W₁ : Disjoint (⁅M, M⁆ : Subgroup G) W₁
  isNilpotent_E : Group.IsNilpotent E
  le_commutator_E : E ≤ ⁅M, M⁆
  le_normalizer_E : W₁ ≤ normalizer (E : Set G)
  sup_hallCore_E : (hallCore M).map M.subtype ⊔ E = ⁅M, M⁆
  disjoint_hallCore_E : Disjoint ((hallCore M).map M.subtype) E
  not_isCyclic_hallCore : ¬ IsCyclic ((hallCore M).map M.subtype)
  commutator_commutator_le_fittingRaw :
    ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ (fittingRaw M).map M.subtype
  coe_fittingRaw_eq : ((fittingRaw M).map M.subtype : Set G) =
    ((hallCore M).map M.subtype : Set G) *
      ((M ⊓ centralizer (((hallCore M).map M.subtype : Subgroup G) : Set G) : Subgroup G) : Set G)
  fittingRaw_le_commutator : (fittingRaw M).map M.subtype ≤ ⁅M, M⁆
  ne_bot_W₂ : W₂ ≠ ⊥
  isCyclic_W₂ : IsCyclic W₂
  le_W₂ : W₂ ≤ (hallCore M).map M.subtype ⊓ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆
  inf_centralizer_eq_W₂ :
    ∀ w ∈ W₁, w ≠ 1 → (⁅M, M⁆ : Subgroup G) ⊓ centralizer {w} = W₂
  isInternalDirectProduct_sup : IsInternalDirectProduct (W₁ ⊔ W₂) W₁ W₂
  isTIWithNormalizer_cyclicTIset : IsTIWithNormalizer (cyclicTIset W₁ W₂) (W₁ ⊔ W₂)

namespace IsWitnessedPConfiguration

variable {M E W₁ W₂ : Subgroup G} (hc : IsWitnessedPConfiguration M E W₁ W₂)

include hc

theorem le_M_W₁ : W₁ ≤ M := hc.sup_commutator_W₁ ▸ le_sup_right

theorem le_M_E : E ≤ M := hc.le_commutator_E.trans (Subgroup.commutator_le_self M)

theorem hallCore_le_commutator : (hallCore M).map M.subtype ≤ ⁅M, M⁆ :=
  hc.sup_hallCore_E ▸ le_sup_left

theorem le_hallCore_W₂ : W₂ ≤ (hallCore M).map M.subtype := hc.le_W₂.trans inf_le_left

theorem le_M_W₂ : W₂ ≤ M :=
  hc.le_hallCore_W₂.trans (hc.hallCore_le_commutator.trans (Subgroup.commutator_le_self M))

theorem le_commutator_commutator_W₂ :
    W₂ ≤ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := hc.le_W₂.trans inf_le_right

theorem le_fittingRaw_W₂ : W₂ ≤ (fittingRaw M).map M.subtype :=
  hc.le_commutator_commutator_W₂.trans hc.commutator_commutator_le_fittingRaw

theorem hallCore_ne_bot : (hallCore M).map M.subtype ≠ ⊥ :=
  fun h => hc.not_isCyclic_hallCore (h ▸ inferInstance)

theorem isComplement'_subgroupOf_commutator_W₁ :
    ((⁅M, M⁆ : Subgroup G).subgroupOf M).IsComplement' (W₁.subgroupOf M) := by
  have := normal_subgroupOf_commutator_self M
  refine (isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_).symm
  · rw [← Subgroup.subgroupOf_sup (Subgroup.commutator_le_self M) hc.le_M_W₁,
      hc.sup_commutator_W₁, Subgroup.subgroupOf_self]
  · rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
      disjoint_iff.1 hc.disjoint_commutator_W₁]
    simp

theorem relIndex_W₁_eq_natCard_commutator :
    W₁.relIndex M = Nat.card (⁅M, M⁆ : Subgroup G) := by
  have h := hc.isComplement'_subgroupOf_commutator_W₁.index_eq_card
  rwa [natCard_subgroupOf (Subgroup.commutator_le_self M)] at h

theorem coprime_natCard_W₁_natCard_commutator :
    (Nat.card W₁).Coprime (Nat.card (⁅M, M⁆ : Subgroup G)) :=
  hc.relIndex_W₁_eq_natCard_commutator ▸ hc.hall_W₁

theorem natCard_M_eq : Nat.card M = Nat.card (⁅M, M⁆ : Subgroup G) * Nat.card W₁ := by
  have h := hc.isComplement'_subgroupOf_commutator_W₁.card_mul_card
  rwa [natCard_subgroupOf (Subgroup.commutator_le_self M), natCard_subgroupOf hc.le_M_W₁,
    eq_comm] at h

theorem normal_subgroupOf_hallCore :
    (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hc.hallCore_le_commutator).2
    (commutator_le_normalizer_hallCore M)

theorem isComplement'_subgroupOf_hallCore_E :
    (((hallCore M).map M.subtype).subgroupOf (⁅M, M⁆ : Subgroup G)).IsComplement'
      (E.subgroupOf (⁅M, M⁆ : Subgroup G)) := by
  have := hc.normal_subgroupOf_hallCore
  refine (isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_).symm
  · rw [← Subgroup.subgroupOf_sup hc.hallCore_le_commutator hc.le_commutator_E,
      hc.sup_hallCore_E, Subgroup.subgroupOf_self]
  · rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf,
      disjoint_iff.1 hc.disjoint_hallCore_E]
    simp

theorem natCard_commutator_eq :
    Nat.card (⁅M, M⁆ : Subgroup G) = Nat.card ((hallCore M).map M.subtype) * Nat.card E := by
  have h := hc.isComplement'_subgroupOf_hallCore_E.card_mul_card
  rwa [natCard_subgroupOf hc.hallCore_le_commutator, natCard_subgroupOf hc.le_commutator_E,
    eq_comm] at h

theorem fittingRaw_eq_sup :
    (fittingRaw M).map M.subtype = (hallCore M).map M.subtype ⊔
      (M ⊓ centralizer (((hallCore M).map M.subtype : Subgroup G) : Set G)) := by
  refine SetLike.coe_injective ?_
  rw [hc.coe_fittingRaw_eq, Subgroup.coe_mul_of_right_le_normalizer_left]
  exact inf_le_left.trans (le_normalizer_map_subtype_hallCore M)

theorem hallCore_le_fittingRaw_map : (hallCore M).map M.subtype ≤ (fittingRaw M).map M.subtype :=
  hc.fittingRaw_eq_sup ▸ le_sup_left

theorem inf_W₁_W₂ : W₁ ⊓ W₂ = ⊥ := hc.isInternalDirectProduct_sup.inf_eq_bot

theorem commute_W₁_W₂ {x y : G} (hx : x ∈ W₁) (hy : y ∈ W₂) : Commute x y :=
  hc.isInternalDirectProduct_sup.commute hx hy

theorem coe_sup_W₁_W₂ : ((W₁ ⊔ W₂ : Subgroup G) : Set G) = (W₁ : Set G) * (W₂ : Set G) :=
  hc.isInternalDirectProduct_sup.coe_eq_mul

theorem le_M_sup_W₁_W₂ : W₁ ⊔ W₂ ≤ M := sup_le hc.le_M_W₁ hc.le_M_W₂

theorem natCard_sup_W₁_W₂ : Nat.card (W₁ ⊔ W₂ : Subgroup G) = Nat.card W₁ * Nat.card W₂ :=
  hc.isInternalDirectProduct_sup.card_eq_mul

theorem normalizer_cyclicTIset : normalizer (cyclicTIset W₁ W₂) = W₁ ⊔ W₂ :=
  hc.isTIWithNormalizer_cyclicTIset.normalizer_eq

theorem disjoint_cyclicTIset_conj {g : G} (hg : g ∉ W₁ ⊔ W₂) :
    Disjoint (cyclicTIset W₁ W₂) (MulAut.conj g '' cyclicTIset W₁ W₂) :=
  hc.isTIWithNormalizer_cyclicTIset.disjoint_conj_image g hg

theorem exists_inf_centralizer_eq_W₂ :
    ∃ w ∈ W₁, w ≠ (1 : G) ∧ (⁅M, M⁆ : Subgroup G) ⊓ centralizer {w} = W₂ := by
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.ne_bot_W₁
  have hw1 : (w : G) ≠ 1 := by simpa using hw
  exact ⟨w, w.2, hw1, hc.inf_centralizer_eq_W₂ _ w.2 hw1⟩

theorem eq_of_eq_W₁ {E' W₂' : Subgroup G} (hc' : IsWitnessedPConfiguration M E' W₁ W₂') :
    W₂ = W₂' := by
  obtain ⟨w, hw, hw1, hcw⟩ := hc.exists_inf_centralizer_eq_W₂
  rw [← hcw, hc'.inf_centralizer_eq_W₂ w hw hw1]

end IsWitnessedPConfiguration

end

end CFSG.FeitThompson
