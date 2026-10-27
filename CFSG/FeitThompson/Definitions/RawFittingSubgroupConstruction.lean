module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X]

def IsPrimePowerOrder (N : Subgroup X) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ n : ℕ, Nat.card N = p ^ n

theorem isPrimePowerOrder_iff {N : Subgroup X} :
    IsPrimePowerOrder N ↔ ∃ p : ℕ, p.Prime ∧ ∃ n : ℕ, Nat.card N = p ^ n := (Iff.rfl)

theorem isPrimePowerOrder_bot : IsPrimePowerOrder (⊥ : Subgroup X) :=
  ⟨2, Nat.prime_two, 0, by simp⟩

theorem isPrimePowerOrder_iff_card_eq_one_or_isPrimePow {N : Subgroup X} :
    IsPrimePowerOrder N ↔ Nat.card N = 1 ∨ IsPrimePow (Nat.card N) := by
  constructor
  · rintro ⟨p, hp, n, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · exact Or.inl (by simpa using hn)
    · exact Or.inr ⟨p, n, Nat.prime_iff.1 hp, hn', hn.symm⟩
  · rintro (h | ⟨p, n, hp, hn, h⟩)
    · exact ⟨2, Nat.prime_two, 0, by simpa using h⟩
    · exact ⟨p, Nat.prime_iff.2 hp, n, h.symm⟩

theorem isPrimePowerOrder_iff_isPGroup [Finite X] {N : Subgroup X} :
    IsPrimePowerOrder N ↔ ∃ p : ℕ, p.Prime ∧ IsPGroup p N := by
  constructor
  · rintro ⟨p, hp, n, hn⟩
    exact ⟨p, hp, IsPGroup.of_card hn⟩
  · rintro ⟨p, hp, hN⟩
    have : Fact p.Prime := ⟨hp⟩
    exact ⟨p, hp, IsPGroup.iff_card.1 hN⟩

theorem isPrimePowerOrder_iff_isPiSubgroup [Finite X] {N : Subgroup X} :
    IsPrimePowerOrder N ↔ ∃ p : ℕ, p.Prime ∧ IsPiSubgroup ({p} : Set ℕ) N := by
  rw [isPrimePowerOrder_iff_isPGroup]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, (isPiSubgroup_singleton_iff hp N).2 h⟩,
    fun ⟨p, hp, h⟩ => ⟨p, hp, (isPiSubgroup_singleton_iff hp N).1 h⟩⟩

def fittingRaw (X : Type*) [Group X] [Finite X] : Subgroup X :=
  sSup {N : Subgroup X | N.Normal ∧ IsPrimePowerOrder N}

variable [Finite X] {N : Subgroup X}

theorem le_fittingRaw (hN : N.Normal) (hN' : IsPrimePowerOrder N) : N ≤ fittingRaw X :=
  le_sSup ⟨hN, hN'⟩

theorem le_fittingRaw_of_isPGroup {p : ℕ} (hp : p.Prime) (hN : N.Normal) (hN' : IsPGroup p N) :
    N ≤ fittingRaw X :=
  le_fittingRaw hN (isPrimePowerOrder_iff_isPGroup.2 ⟨p, hp, hN'⟩)

theorem fittingRaw_le {K : Subgroup X}
    (h : ∀ N : Subgroup X, N.Normal → IsPrimePowerOrder N → N ≤ K) : fittingRaw X ≤ K :=
  sSup_le fun _ hN => h _ hN.1 hN.2

theorem fittingRaw_le_iff {K : Subgroup X} :
    fittingRaw X ≤ K ↔ ∀ N : Subgroup X, N.Normal → IsPrimePowerOrder N → N ≤ K :=
  ⟨fun h _ hN hN' => (le_fittingRaw hN hN').trans h, fittingRaw_le⟩

theorem fittingRaw_eq_closure (X : Type*) [Group X] [Finite X] :
    fittingRaw X =
      Subgroup.closure {x | ∃ N : Subgroup X, N.Normal ∧ IsPrimePowerOrder N ∧ x ∈ N} := by
  refine le_antisymm
    (fittingRaw_le fun N hN hN' x hx => Subgroup.subset_closure ⟨N, hN, hN', hx⟩) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨N, hN, hN', hx⟩
  exact le_fittingRaw hN hN' hx

theorem pCore_le_fittingRaw {p : ℕ} (hp : p.Prime) : pCore p X ≤ fittingRaw X := by
  rw [pCore_eq_piCore]
  exact piCore_le fun N hN hπ =>
    le_fittingRaw hN (isPrimePowerOrder_iff_isPiSubgroup.2 ⟨p, hp, hπ⟩)

theorem fittingRaw_eq_iSup_pCore (X : Type*) [Group X] [Finite X] :
    fittingRaw X = ⨆ p ∈ {p : ℕ | p.Prime}, pCore p X := by
  refine le_antisymm (fittingRaw_le fun N hN hN' => ?_)
    (iSup₂_le fun p hp => pCore_le_fittingRaw hp)
  obtain ⟨p, hp, hN'⟩ := isPrimePowerOrder_iff_isPiSubgroup.1 hN'
  refine le_trans ?_ (le_iSup₂ (f := fun p (_ : p ∈ {p : ℕ | p.Prime}) => pCore p X) p hp)
  rw [pCore_eq_piCore]
  exact le_piCore hN hN'

theorem fittingRaw_eq_bot_of_subsingleton (X : Type*) [Group X] [Finite X] [Subsingleton X] :
    fittingRaw X = ⊥ := Subsingleton.elim _ _

theorem fittingRaw_eq_top_of_isPGroup {p : ℕ} (hp : p.Prime) (hX : IsPGroup p X) :
    fittingRaw X = ⊤ :=
  eq_top_iff.2 <| le_fittingRaw_of_isPGroup hp (Subgroup.normal_of_characteristic ⊤)
    (hX.to_subgroup ⊤)

end

end CFSG.FeitThompson
