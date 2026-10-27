module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
public import Mathlib.GroupTheory.Sylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem piCore_eq_sSup (π : Set ℕ) (X : Type*) [Group X] [Finite X] :
    piCore π X = sSup {N : Subgroup X | N.Normal ∧ IsPiSubgroup π N} :=
  le_antisymm (piCore_le fun _ hN hπ => le_sSup ⟨hN, hπ⟩)
    (sSup_le fun _ hN => le_piCore hN.1 hN.2)

theorem map_piCore (π : Set ℕ) (X : Type*) [Group X] [Finite X] (φ : X ≃* X) :
    (piCore π X).map φ.toMonoidHom = piCore π X :=
  Subgroup.characteristic_iff_map_eq.1 (piCore_characteristic π X) φ

theorem map_pCore (p : ℕ) (X : Type*) [Group X] [Finite X] (φ : X ≃* X) :
    (pCore p X).map φ.toMonoidHom = pCore p X :=
  Subgroup.characteristic_iff_map_eq.1 (pCore_characteristic p X) φ

theorem pCore_normal (p : ℕ) (X : Type*) [Group X] [Finite X] : (pCore p X).Normal :=
  Subgroup.normal_of_characteristic _

theorem pCore_eq_sSup_normal_isPGroup (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    pCore p X = sSup {N : Subgroup X | N.Normal ∧ IsPGroup p N} := by
  rw [pCore_eq_piCore, piCore_eq_sSup]
  congr 1
  ext N
  simp [isPiSubgroup_singleton_iff hp]

theorem exists_card_pCore_eq_pow (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    ∃ n : ℕ, Nat.card (pCore p X) = p ^ n :=
  have : Fact p.Prime := ⟨hp⟩
  IsPGroup.iff_card.1 (isPGroup_pCore hp X)

theorem isPrimePowerOrder_pCore (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    IsPrimePowerOrder (pCore p X) :=
  isPrimePowerOrder_iff_isPGroup.2 ⟨p, hp, isPGroup_pCore hp X⟩

theorem isGreatest_pCore (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    IsGreatest {N : Subgroup X | N.Normal ∧ IsPGroup p N} (pCore p X) :=
  ⟨⟨pCore_normal p X, isPGroup_pCore hp X⟩, fun _ hN => le_pCore hp hN.1 hN.2⟩

theorem normal_isPGroup_iff_le_pCore (hp : p.Prime) {N : Subgroup X} :
    N.Normal ∧ IsPGroup p N ↔ N.Normal ∧ N ≤ pCore p X :=
  ⟨fun h => ⟨h.1, le_pCore hp h.1 h.2⟩,
    fun h => ⟨h.1, (isPGroup_pCore hp X).to_le h.2⟩⟩

theorem pCore_eq_top_of_isPGroup (hp : p.Prime) (hX : IsPGroup p X) : pCore p X = ⊤ :=
  eq_top_iff.2 (le_pCore hp (Subgroup.normal_of_characteristic ⊤) (hX.to_subgroup ⊤))

theorem pCore_le_sylow (hp : p.Prime) (P : Sylow p X) : pCore p X ≤ (P : Subgroup X) :=
  have : Fact p.Prime := ⟨hp⟩
  have := pCore_normal p X
  (isPGroup_pCore hp X).le_sylow_of_normal P

end

end CFSG.FeitThompson
