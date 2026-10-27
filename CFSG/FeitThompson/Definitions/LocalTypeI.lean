module

public import CFSG.FeitThompson.Definitions.MaximumElementaryAbelianPrimeRank
public import CFSG.FeitThompson.Definitions.TISubsetWithItsExactNormalizer
public import CFSG.FeitThompson.Definitions.TheLocalFrobeniusTypePredicate

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {M : Subgroup G}

def hallCoreSharp (M : Subgroup G) : Set G := ((hallCore M).map M.subtype : Set G) \ {1}

theorem hallCoreSharp_eq (M : Subgroup G) :
    hallCoreSharp M = ((hallCore M).map M.subtype : Set G) \ {1} := (rfl)

@[simp]
theorem mem_hallCoreSharp {g : G} :
    g ∈ hallCoreSharp M ↔ g ∈ (hallCore M).map M.subtype ∧ g ≠ 1 := Iff.rfl

theorem mem_hallCoreSharp_of_mem {x : M} (hx : x ∈ hallCore M) (hx1 : (x : G) ≠ 1) :
    (x : G) ∈ hallCoreSharp M :=
  ⟨Subgroup.mem_map_of_mem _ hx, hx1⟩

@[simp]
theorem one_notMem_hallCoreSharp (M : Subgroup G) : (1 : G) ∉ hallCoreSharp M := by simp

theorem hallCoreSharp_nonempty_iff : (hallCoreSharp M).Nonempty ↔ hallCore M ≠ ⊥ := by
  refine ⟨fun ⟨g, hg, hg1⟩ h => ?_, fun h => ?_⟩
  · rw [h] at hg
    exact hg1 (by simpa using hg)
  · obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
    refine ⟨((x : M) : G), mem_hallCoreSharp_of_mem x.2 fun hc => hx ?_⟩
    ext
    simpa using hc

theorem hallCoreSharp_subset_coe (M : Subgroup G) : hallCoreSharp M ⊆ (M : Set G) := by
  rintro g ⟨hg, -⟩
  obtain ⟨x, -, rfl⟩ := hg
  exact x.2

structure IsTypeI {G : Type*} [Group G] [Finite G] (M : Subgroup G) : Prop where
  lt_top : M < ⊤
  exists_isFrobeniusType : ∃ E : Subgroup M, IsFrobeniusType M E ∧
    (IsTIWithNormalizer (hallCoreSharp M) M ∨
      (IsMulCommutative (hallCore M) ∧ maxElementaryAbelianPRank (hallCore M) = 2) ∨
      ((∀ r ∈ (Nat.card (hallCore M)).primeFactors, Monoid.exponent E ∣ r - 1) ∧
        ∃ r ∈ (Nat.card (hallCore M)).primeFactors, IsCyclic (pComplCore r (hallCore M))))

namespace IsTypeI

variable [Finite G]

theorem of_isTIWithNormalizer {E : Subgroup M} (hM : M < ⊤) (hE : IsFrobeniusType M E)
    (h : IsTIWithNormalizer (hallCoreSharp M) M) : IsTypeI M :=
  ⟨hM, E, hE, Or.inl h⟩

theorem of_abelian_rank_eq_two {E : Subgroup M} (hM : M < ⊤) (hE : IsFrobeniusType M E)
    (habel : IsMulCommutative (hallCore M))
    (hrank : maxElementaryAbelianPRank (hallCore M) = 2) : IsTypeI M :=
  ⟨hM, E, hE, Or.inr (Or.inl ⟨habel, hrank⟩)⟩

theorem of_exponent_dvd_of_isCyclic {E : Subgroup M} (hM : M < ⊤) (hE : IsFrobeniusType M E)
    (hexp : ∀ r ∈ (Nat.card (hallCore M)).primeFactors, Monoid.exponent E ∣ r - 1)
    (hcyc : ∃ r ∈ (Nat.card (hallCore M)).primeFactors, IsCyclic (pComplCore r (hallCore M))) :
    IsTypeI M :=
  ⟨hM, E, hE, Or.inr (Or.inr ⟨hexp, hcyc⟩)⟩

theorem ne_top (h : IsTypeI M) : M ≠ ⊤ := h.lt_top.ne

theorem exists_frobenius (h : IsTypeI M) : ∃ E : Subgroup M, IsFrobeniusType M E := by
  obtain ⟨E, hE, -⟩ := h.exists_isFrobeniusType
  exact ⟨E, hE⟩

theorem bot_lt_hallCore (h : IsTypeI M) : ⊥ < hallCore M := by
  obtain ⟨E, hE⟩ := h.exists_frobenius
  exact hE.bot_lt_hallCore

theorem hallCore_lt_top (h : IsTypeI M) : hallCore M < ⊤ := by
  obtain ⟨E, hE⟩ := h.exists_frobenius
  exact hE.hallCore_lt_top

theorem hallCore_ne_bot (h : IsTypeI M) : hallCore M ≠ ⊥ := h.bot_lt_hallCore.ne'

theorem hallCore_ne_top (h : IsTypeI M) : hallCore M ≠ ⊤ := h.hallCore_lt_top.ne

theorem hallCoreSharp_nonempty (h : IsTypeI M) : (hallCoreSharp M).Nonempty :=
  hallCoreSharp_nonempty_iff.2 h.hallCore_ne_bot

theorem nontrivial (h : IsTypeI M) : Nontrivial M := by
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.hallCore_ne_bot
  exact ⟨⟨(x : M), 1, fun hc => hx (Subtype.ext hc)⟩⟩

theorem exists_isFrobeniusType_or (h : IsTypeI M) :
    ∃ E : Subgroup M, IsFrobeniusType M E ∧
      (IsTIWithNormalizer (hallCoreSharp M) M ∨
        (IsMulCommutative (hallCore M) ∧ maxElementaryAbelianPRank (hallCore M) = 2) ∨
        ((∀ r ∈ (Nat.card (hallCore M)).primeFactors, Monoid.exponent E ∣ r - 1) ∧
          ∃ r ∈ (Nat.card (hallCore M)).primeFactors, IsCyclic (pComplCore r (hallCore M)))) :=
  h.exists_isFrobeniusType

theorem elim {p : Prop} (h : IsTypeI M)
    (hi : ∀ E : Subgroup M, IsFrobeniusType M E → IsTIWithNormalizer (hallCoreSharp M) M → p)
    (hii : ∀ E : Subgroup M, IsFrobeniusType M E → IsMulCommutative (hallCore M) →
      maxElementaryAbelianPRank (hallCore M) = 2 → p)
    (hiii : ∀ E : Subgroup M, IsFrobeniusType M E →
      (∀ r ∈ (Nat.card (hallCore M)).primeFactors, Monoid.exponent E ∣ r - 1) →
      (∃ r ∈ (Nat.card (hallCore M)).primeFactors, IsCyclic (pComplCore r (hallCore M))) → p) :
    p := by
  obtain ⟨E, hE, hcase | ⟨habel, hrank⟩ | ⟨hexp, hcyc⟩⟩ := h.exists_isFrobeniusType
  · exact hi E hE hcase
  · exact hii E hE habel hrank
  · exact hiii E hE hexp hcyc

end IsTypeI

end

end CFSG.FeitThompson
