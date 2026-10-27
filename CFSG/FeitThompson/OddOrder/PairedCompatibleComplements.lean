module

public import CFSG.FeitThompson.OddOrder.PairedMaximalSubgroupsSwap
import CFSG.FeitThompson.OddOrder.PConfigAlignDerivedComplement
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
import CFSG.FeitThompson.OddOrder.PairedSecondFactorIdentification

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {M S T E W₁ W₂ : Subgroup G}

structure IsTypeClausesWitness (M E W₁ W₂ : Subgroup G) : Prop where
  typeII : IsTypeII M → IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
    ¬ normalizer (E : Set G) ≤ M ∧
    IsFrobeniusType ↥(⁅M, M⁆ : Subgroup G) (E.subgroupOf (⁅M, M⁆ : Subgroup G)) ∧
    (hallCore ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype =
      (hallCore M).map M.subtype
  typeIII : IsTypeIII M → IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
    normalizer (E : Set G) ≤ M
  typeIV : IsTypeIV M → IsPConfigurationIIToIV M E W₁ W₂ ∧ ¬ IsMulCommutative E ∧
    normalizer (E : Set G) ≤ M
  typeV : IsTypeV M → E = ⊥ ∧ (IsTIWithNormalizer (hallCoreSharp M) M ∨
    (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
      IsCyclic (pComplCore r (hallCore M)) ∧ Nat.card W₁ ∣ r - 1) ∨
    (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
      IsCyclic (pComplCore r (hallCore M)) ∧
        Nat.card (pCore r (hallCore M)) = r ^ 3 ∧ Nat.card W₁ ∣ r + 1))

theorem isTypeClausesWitness_of_isWitnessedPConfiguration (hsolv : Group.IsSolvable M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) : IsTypeClausesWitness M E W₁ W₂ where
  typeII h := h.clauses_of_isWitnessedPConfiguration hsolv hc
  typeIII h := h.clauses_of_isWitnessedPConfiguration hsolv hc
  typeIV h := h.clauses_of_isWitnessedPConfiguration hsolv hc
  typeV h := h.clauses_of_isWitnessedPConfiguration hsolv hc

namespace IsTypeClausesWitness

variable (hw : IsTypeClausesWitness M E W₁ W₂)

include hw

theorem isPConfigurationIIToIV (h : IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M) :
    IsPConfigurationIIToIV M E W₁ W₂ := by
  rcases h with h | h | h
  · exact (hw.typeII h).1
  · exact (hw.typeIII h).1
  · exact (hw.typeIV h).1

theorem eq_bot_of_isTypeV (h : IsTypeV M) : E = ⊥ := (hw.typeV h).1

end IsTypeClausesWitness

namespace IsTypePPair

theorem exists_isWitnessedPConfiguration_left (hp : IsTypePPair S T W₁ W₂) :
    ∃ E₀ V₁ V₂ : Subgroup G, IsWitnessedPConfiguration S E₀ V₁ V₂ := by
  rcases hp.typeIIToV_left with h | h | h | h
  · obtain ⟨E₀, V₁, V₂, hc⟩ := h.exists_isPConfiguration
    exact ⟨E₀, V₁, V₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨E₀, V₁, V₂, hc⟩ := h.exists_isPConfiguration
    exact ⟨E₀, V₁, V₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨E₀, V₁, V₂, hc⟩ := h.exists_isPConfiguration
    exact ⟨E₀, V₁, V₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨V₁, V₂, hc⟩ := h.exists_isWitnessedPConfiguration_bot
    exact ⟨⊥, V₁, V₂, hc⟩

theorem exists_isWitnessedPConfiguration_right (hp : IsTypePPair S T W₁ W₂) :
    ∃ E₀ V₁ V₂ : Subgroup G, IsWitnessedPConfiguration T E₀ V₁ V₂ :=
  hp.symm.exists_isWitnessedPConfiguration_left

theorem exists_compatible_left (hp : IsTypePPair S T W₁ W₂) :
    ∃ U ≤ S, IsWitnessedPConfiguration S U W₁ W₂ ∧ IsTypeClausesWitness S U W₁ W₂ := by
  have hsolv := hp.isSolvable S hp.ne_top_left
  obtain ⟨E₀, V₁, V₂, hc⟩ := hp.exists_isWitnessedPConfiguration_left
  obtain ⟨y, -, -, hy⟩ := exists_mem_map_conj_eq_and_isWitnessedPConfiguration hc
    hp.sup_commutator_left hp.disjoint_commutator_left
  have hy' := hp.isWitnessedPConfiguration_W₂ hy
  exact ⟨_, hy'.le_M_E, hy', isTypeClausesWitness_of_isWitnessedPConfiguration hsolv hy'⟩

theorem exists_compatible_right (hp : IsTypePPair S T W₁ W₂) :
    ∃ V ≤ T, IsWitnessedPConfiguration T V W₂ W₁ ∧ IsTypeClausesWitness T V W₂ W₁ :=
  hp.symm.exists_compatible_left

theorem exists_compatible_pair (hp : IsTypePPair S T W₁ W₂) :
    ∃ U ≤ S, ∃ V ≤ T,
      (IsWitnessedPConfiguration S U W₁ W₂ ∧ IsTypeClausesWitness S U W₁ W₂) ∧
        (IsWitnessedPConfiguration T V W₂ W₁ ∧ IsTypeClausesWitness T V W₂ W₁) := by
  obtain ⟨U, hUS, hU⟩ := hp.exists_compatible_left
  obtain ⟨V, hVT, hV⟩ := hp.exists_compatible_right
  exact ⟨U, hUS, V, hVT, hU, hV⟩

end IsTypePPair

end

end CFSG.FeitThompson
