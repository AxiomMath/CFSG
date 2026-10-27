module

public import CFSG.FeitThompson.Definitions.TheWitnessedPConfiguration
public import CFSG.FeitThompson.Definitions.LocalTypeI

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {M E W₁ W₂ : Subgroup G}

def fittingRawSharp (M : Subgroup G) : Set G :=
  ((fittingRaw M).map M.subtype : Set G) \ {1}

theorem fittingRawSharp_eq (M : Subgroup G) :
    fittingRawSharp M = ((fittingRaw M).map M.subtype : Set G) \ {1} := (rfl)

@[simp]
theorem mem_fittingRawSharp {g : G} :
    g ∈ fittingRawSharp M ↔ g ∈ (fittingRaw M).map M.subtype ∧ g ≠ 1 := Iff.rfl

theorem mem_fittingRawSharp_of_mem {x : M} (hx : x ∈ fittingRaw M) (hx1 : (x : G) ≠ 1) :
    (x : G) ∈ fittingRawSharp M :=
  ⟨Subgroup.mem_map_of_mem _ hx, hx1⟩

@[simp]
theorem one_notMem_fittingRawSharp (M : Subgroup G) : (1 : G) ∉ fittingRawSharp M := by simp

theorem fittingRawSharp_nonempty_iff : (fittingRawSharp M).Nonempty ↔ fittingRaw M ≠ ⊥ := by
  refine ⟨fun ⟨g, hg, hg1⟩ h => ?_, fun h => ?_⟩
  · rw [h] at hg
    exact hg1 (by simpa using hg)
  · obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    refine ⟨((x : M) : G), mem_fittingRawSharp_of_mem x.2 fun hc => hx ?_⟩
    ext
    simpa using hc

theorem fittingRawSharp_subset_coe (M : Subgroup G) : fittingRawSharp M ⊆ (M : Set G) := by
  rintro g ⟨hg, -⟩
  obtain ⟨x, -, rfl⟩ := hg
  exact x.2

theorem hallCoreSharp_subset_fittingRawSharp (M : Subgroup G) :
    hallCoreSharp M ⊆ fittingRawSharp M := by
  rw [hallCoreSharp_eq, fittingRawSharp_eq]
  exact Set.sdiff_subset_sdiff_left (SetLike.coe_subset_coe.2
    ((Subgroup.map_le_map_iff_of_injective M.subtype_injective).2 hallCore_le_fittingRaw))

namespace IsWitnessedPConfiguration

variable (hc : IsWitnessedPConfiguration M E W₁ W₂)

include hc

theorem hallCore_ne_bot' : hallCore M ≠ ⊥ := fun h =>
  hc.hallCore_ne_bot (by rw [h, Subgroup.map_bot])

theorem fittingRaw_ne_bot : fittingRaw M ≠ ⊥ := fun h =>
  hc.hallCore_ne_bot' (le_bot_iff.mp (hallCore_le_fittingRaw.trans h.le))

theorem hallCoreSharp_nonempty : (hallCoreSharp M).Nonempty :=
  hallCoreSharp_nonempty_iff.2 hc.hallCore_ne_bot'

theorem fittingRawSharp_nonempty : (fittingRawSharp M).Nonempty :=
  fittingRawSharp_nonempty_iff.2 hc.fittingRaw_ne_bot

end IsWitnessedPConfiguration

structure IsPConfigurationIIToIV (M E W₁ W₂ : Subgroup G) : Prop where
  isWitnessedPConfiguration : IsWitnessedPConfiguration M E W₁ W₂
  prime_natCard_W₁ : (Nat.card W₁).Prime
  isTIWithNormalizer_fittingRawSharp : IsTIWithNormalizer (fittingRawSharp M) M

namespace IsPConfigurationIIToIV

variable (hc : IsPConfigurationIIToIV M E W₁ W₂)

include hc

theorem lt_top : M < ⊤ := hc.isWitnessedPConfiguration.lt_top

theorem ne_top : M ≠ ⊤ := hc.lt_top.ne

theorem ne_bot_W₁ : W₁ ≠ ⊥ := hc.isWitnessedPConfiguration.ne_bot_W₁

theorem normalizer_fittingRawSharp : normalizer (fittingRawSharp M) = M :=
  hc.isTIWithNormalizer_fittingRawSharp.normalizer_eq

end IsPConfigurationIIToIV

structure IsTypeII (M : Subgroup G) : Prop where
  exists_isPConfigurationIIToIV : ∃ E W₁ W₂ : Subgroup G,
    IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
      ¬ normalizer (E : Set G) ≤ M ∧
      IsFrobeniusType ↥(⁅M, M⁆ : Subgroup G) (E.subgroupOf (⁅M, M⁆ : Subgroup G)) ∧
      (hallCore ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype =
        (hallCore M).map M.subtype

namespace IsTypeII

theorem mk' (hc : IsPConfigurationIIToIV M E W₁ W₂) (hE : E ≠ ⊥) (habel : IsMulCommutative E)
    (hnorm : ¬ normalizer (E : Set G) ≤ M)
    (hfrob : IsFrobeniusType ↥(⁅M, M⁆ : Subgroup G) (E.subgroupOf (⁅M, M⁆ : Subgroup G)))
    (hhall : (hallCore ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype =
      (hallCore M).map M.subtype) : IsTypeII M :=
  ⟨E, W₁, W₂, hc, hE, habel, hnorm, hfrob, hhall⟩

variable (h : IsTypeII M)

include h

theorem exists_isPConfiguration : ∃ E W₁ W₂ : Subgroup G, IsPConfigurationIIToIV M E W₁ W₂ := by
  obtain ⟨E, W₁, W₂, hc, -⟩ := h.exists_isPConfigurationIIToIV
  exact ⟨E, W₁, W₂, hc⟩

theorem lt_top : M < ⊤ := by
  obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
  exact hc.lt_top

theorem ne_top : M ≠ ⊤ := h.lt_top.ne

theorem isTIWithNormalizer_fittingRawSharp : IsTIWithNormalizer (fittingRawSharp M) M := by
  obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
  exact hc.isTIWithNormalizer_fittingRawSharp

end IsTypeII

structure IsTypeIII (M : Subgroup G) : Prop where
  exists_isPConfigurationIIToIV : ∃ E W₁ W₂ : Subgroup G,
    IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ IsMulCommutative E ∧
      normalizer (E : Set G) ≤ M

namespace IsTypeIII

theorem mk' (hc : IsPConfigurationIIToIV M E W₁ W₂) (hE : E ≠ ⊥) (habel : IsMulCommutative E)
    (hnorm : normalizer (E : Set G) ≤ M) : IsTypeIII M :=
  ⟨E, W₁, W₂, hc, hE, habel, hnorm⟩

variable (h : IsTypeIII M)

include h

theorem exists_isPConfiguration : ∃ E W₁ W₂ : Subgroup G, IsPConfigurationIIToIV M E W₁ W₂ := by
  obtain ⟨E, W₁, W₂, hc, -⟩ := h.exists_isPConfigurationIIToIV
  exact ⟨E, W₁, W₂, hc⟩

theorem lt_top : M < ⊤ := by
  obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
  exact hc.lt_top

theorem ne_top : M ≠ ⊤ := h.lt_top.ne

theorem isTIWithNormalizer_fittingRawSharp : IsTIWithNormalizer (fittingRawSharp M) M := by
  obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
  exact hc.isTIWithNormalizer_fittingRawSharp

end IsTypeIII

structure IsTypeIV (M : Subgroup G) : Prop where
  exists_isPConfigurationIIToIV : ∃ E W₁ W₂ : Subgroup G,
    IsPConfigurationIIToIV M E W₁ W₂ ∧ ¬ IsMulCommutative E ∧ normalizer (E : Set G) ≤ M

namespace IsTypeIV

theorem mk' (hc : IsPConfigurationIIToIV M E W₁ W₂) (habel : ¬ IsMulCommutative E)
    (hnorm : normalizer (E : Set G) ≤ M) : IsTypeIV M :=
  ⟨E, W₁, W₂, hc, habel, hnorm⟩

theorem ne_bot_E (h : IsTypeIV M) : ∃ E W₁ W₂ : Subgroup G,
    IsPConfigurationIIToIV M E W₁ W₂ ∧ E ≠ ⊥ ∧ ¬ IsMulCommutative E ∧
      normalizer (E : Set G) ≤ M := by
  obtain ⟨E, W₁, W₂, hc, habel, hnorm⟩ := h.exists_isPConfigurationIIToIV
  exact ⟨E, W₁, W₂, hc, fun hE => habel (hE ▸ inferInstance), habel, hnorm⟩

variable (h : IsTypeIV M)

include h

theorem exists_isPConfiguration : ∃ E W₁ W₂ : Subgroup G, IsPConfigurationIIToIV M E W₁ W₂ := by
  obtain ⟨E, W₁, W₂, hc, -⟩ := h.exists_isPConfigurationIIToIV
  exact ⟨E, W₁, W₂, hc⟩

theorem lt_top : M < ⊤ := by
  obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
  exact hc.lt_top

theorem ne_top : M ≠ ⊤ := h.lt_top.ne

theorem isTIWithNormalizer_fittingRawSharp : IsTIWithNormalizer (fittingRawSharp M) M := by
  obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
  exact hc.isTIWithNormalizer_fittingRawSharp

end IsTypeIV

structure IsTypeV (M : Subgroup G) : Prop where
  exists_isWitnessedPConfiguration : ∃ W₁ W₂ : Subgroup G,
    IsWitnessedPConfiguration M ⊥ W₁ W₂ ∧
      (IsTIWithNormalizer (hallCoreSharp M) M ∨
        (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
          IsCyclic (pComplCore r (hallCore M)) ∧ Nat.card W₁ ∣ r - 1) ∨
        (∃ r ∈ (Nat.card (hallCore M)).primeFactors,
          IsCyclic (pComplCore r (hallCore M)) ∧
            Nat.card (pCore r (hallCore M)) = r ^ 3 ∧ Nat.card W₁ ∣ r + 1))

namespace IsTypeV

theorem of_isTIWithNormalizer (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂)
    (h : IsTIWithNormalizer (hallCoreSharp M) M) : IsTypeV M :=
  ⟨W₁, W₂, hc, Or.inl h⟩

theorem of_dvd_sub_one (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) {r : ℕ}
    (hr : r ∈ (Nat.card (hallCore M)).primeFactors) (hcyc : IsCyclic (pComplCore r (hallCore M)))
    (hdvd : Nat.card W₁ ∣ r - 1) : IsTypeV M :=
  ⟨W₁, W₂, hc, Or.inr (Or.inl ⟨r, hr, hcyc, hdvd⟩)⟩

theorem of_dvd_add_one (hc : IsWitnessedPConfiguration M ⊥ W₁ W₂) {r : ℕ}
    (hr : r ∈ (Nat.card (hallCore M)).primeFactors) (hcyc : IsCyclic (pComplCore r (hallCore M)))
    (hcard : Nat.card (pCore r (hallCore M)) = r ^ 3) (hdvd : Nat.card W₁ ∣ r + 1) : IsTypeV M :=
  ⟨W₁, W₂, hc, Or.inr (Or.inr ⟨r, hr, hcyc, hcard, hdvd⟩)⟩

variable (h : IsTypeV M)

include h

theorem exists_isWitnessedPConfiguration_bot :
    ∃ W₁ W₂ : Subgroup G, IsWitnessedPConfiguration M ⊥ W₁ W₂ := by
  obtain ⟨W₁, W₂, hc, -⟩ := h.exists_isWitnessedPConfiguration
  exact ⟨W₁, W₂, hc⟩

theorem lt_top : M < ⊤ := by
  obtain ⟨W₁, W₂, hc⟩ := h.exists_isWitnessedPConfiguration_bot
  exact hc.lt_top

theorem ne_top : M ≠ ⊤ := h.lt_top.ne

theorem map_hallCore_eq_commutator : (hallCore M).map M.subtype = ⁅M, M⁆ := by
  obtain ⟨W₁, W₂, hc⟩ := h.exists_isWitnessedPConfiguration_bot
  simpa using hc.sup_hallCore_E

theorem not_isCyclic_hallCore : ¬ IsCyclic ((hallCore M).map M.subtype) := by
  obtain ⟨W₁, W₂, hc⟩ := h.exists_isWitnessedPConfiguration_bot
  exact hc.not_isCyclic_hallCore

theorem elim {p : Prop}
    (hi : ∀ W₁ W₂ : Subgroup G, IsWitnessedPConfiguration M ⊥ W₁ W₂ →
      IsTIWithNormalizer (hallCoreSharp M) M → p)
    (hii : ∀ W₁ W₂ : Subgroup G, IsWitnessedPConfiguration M ⊥ W₁ W₂ →
      ∀ r ∈ (Nat.card (hallCore M)).primeFactors, IsCyclic (pComplCore r (hallCore M)) →
        Nat.card W₁ ∣ r - 1 → p)
    (hiii : ∀ W₁ W₂ : Subgroup G, IsWitnessedPConfiguration M ⊥ W₁ W₂ →
      ∀ r ∈ (Nat.card (hallCore M)).primeFactors, IsCyclic (pComplCore r (hallCore M)) →
        Nat.card (pCore r (hallCore M)) = r ^ 3 → Nat.card W₁ ∣ r + 1 → p) : p := by
  obtain ⟨W₁, W₂, hc, h1 | ⟨r, hr, hcyc, hdvd⟩ | ⟨r, hr, hcyc, hcard, hdvd⟩⟩ :=
    h.exists_isWitnessedPConfiguration
  · exact hi W₁ W₂ hc h1
  · exact hii W₁ W₂ hc r hr hcyc hdvd
  · exact hiii W₁ W₂ hc r hr hcyc hcard hdvd

end IsTypeV

end

end CFSG.FeitThompson
