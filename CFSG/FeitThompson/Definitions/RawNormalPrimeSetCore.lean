module

public import Mathlib.GroupTheory.PGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X]

def IsPiSubgroup (π : Set ℕ) (N : Subgroup X) : Prop :=
  ∀ p ∈ (Nat.card N).primeFactors, p ∈ π

theorem isPiSubgroup_iff {π : Set ℕ} {N : Subgroup X} :
    IsPiSubgroup π N ↔ ∀ p ∈ (Nat.card N).primeFactors, p ∈ π := (Iff.rfl)

theorem IsPiSubgroup.mono {π π' : Set ℕ} {N : Subgroup X} (h : IsPiSubgroup π N) (hπ : π ⊆ π') :
    IsPiSubgroup π' N := fun p hp => hπ (h p hp)

theorem isPiSubgroup_bot (π : Set ℕ) : IsPiSubgroup π (⊥ : Subgroup X) := by
  simp [IsPiSubgroup]

theorem IsPiSubgroup.of_le [Finite X] {π : Set ℕ} {N M : Subgroup X} (hM : IsPiSubgroup π M)
    (h : N ≤ M) : IsPiSubgroup π N := fun p hp =>
  hM p (Nat.primeFactors_mono (Subgroup.card_dvd_of_le h) Nat.card_pos.ne' hp)

theorem isPiSubgroup_singleton_iff [Finite X] {p : ℕ} (hp : p.Prime) (N : Subgroup X) :
    IsPiSubgroup ({p} : Set ℕ) N ↔ IsPGroup p N := by
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hp.primeFactors, isPiSubgroup_iff]
  simp [Finset.subset_iff]

def piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  sSup {N : Subgroup X | N.Normal ∧ IsPiSubgroup π N}

def pCore (p : ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X := piCore {p} X

def pComplCore (p : ℕ) (X : Type*) [Group X] [Finite X] : Subgroup X :=
  piCore {q : ℕ | q.Prime ∧ q ≠ p} X

variable [Finite X] {π π' : Set ℕ} {N : Subgroup X}

theorem pCore_eq_piCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pCore p X = piCore {p} X := (rfl)

theorem pComplCore_eq_piCore (p : ℕ) (X : Type*) [Group X] [Finite X] :
    pComplCore p X = piCore {q : ℕ | q.Prime ∧ q ≠ p} X := (rfl)

theorem le_piCore (hN : N.Normal) (hπ : IsPiSubgroup π N) : N ≤ piCore π X :=
  le_sSup ⟨hN, hπ⟩

theorem piCore_le {K : Subgroup X}
    (h : ∀ N : Subgroup X, N.Normal → IsPiSubgroup π N → N ≤ K) : piCore π X ≤ K :=
  sSup_le fun N hN => h N hN.1 hN.2

theorem piCore_le_iff {K : Subgroup X} :
    piCore π X ≤ K ↔ ∀ N : Subgroup X, N.Normal → IsPiSubgroup π N → N ≤ K :=
  ⟨fun h _ hN hπ => (le_piCore hN hπ).trans h, piCore_le⟩

theorem piCore_mono (h : π ⊆ π') : piCore π X ≤ piCore π' X :=
  piCore_le fun _ hN hπ => le_piCore hN (hπ.mono h)

theorem piCore_eq_closure (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    piCore π X =
      Subgroup.closure {x | ∃ N : Subgroup X, N.Normal ∧ IsPiSubgroup π N ∧ x ∈ N} := by
  refine le_antisymm (piCore_le fun N hN hπ x hx => Subgroup.subset_closure ⟨N, hN, hπ, hx⟩) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨N, hN, hπ, hx⟩
  exact le_piCore hN hπ hx

theorem piCore_univ (X : Type*) [Group X] [Finite X] : piCore Set.univ X = ⊤ :=
  eq_top_iff.2 (le_piCore (Subgroup.normal_of_characteristic ⊤) fun _ _ => Set.mem_univ _)

theorem piCore_empty (X : Type*) [Group X] [Finite X] : piCore (∅ : Set ℕ) X = ⊥ := by
  refine le_bot_iff.1 (piCore_le fun N _ hπ => ?_)
  have h : (Nat.card N).primeFactors = ∅ := by
    ext p; simpa using fun hp => hπ p hp
  rcases Nat.primeFactors_eq_empty.1 h with h | h
  · exact absurd h Nat.card_pos.ne'
  · exact le_of_eq (Subgroup.card_eq_one.1 h)

theorem le_pCore {p : ℕ} (hp : p.Prime) (hN : N.Normal) (hN' : IsPGroup p N) : N ≤ pCore p X :=
  le_piCore hN ((isPiSubgroup_singleton_iff hp N).2 hN')

theorem le_pComplCore {p : ℕ} (hN : N.Normal) (hN' : p ∉ (Nat.card N).primeFactors) :
    N ≤ pComplCore p X :=
  le_piCore hN fun _ hq => ⟨Nat.prime_of_mem_primeFactors hq, fun h => hN' (h ▸ hq)⟩

end

end CFSG.FeitThompson
