module

public import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {M : Type*} [Group M] [Finite M] {N : Subgroup M}

def alphaCore (M : Type*) [Group M] [Finite M] : Subgroup M :=
  piCore (alphaPrimes M) M

theorem alphaCore_eq_piCore (M : Type*) [Group M] [Finite M] :
    alphaCore M = piCore (alphaPrimes M) M := (rfl)

theorem le_alphaCore (hN : N.Normal) (hπ : IsPiSubgroup (alphaPrimes M) N) : N ≤ alphaCore M :=
  le_piCore hN hπ

theorem alphaCore_le {K : Subgroup M}
    (h : ∀ N : Subgroup M, N.Normal → IsPiSubgroup (alphaPrimes M) N → N ≤ K) : alphaCore M ≤ K :=
  piCore_le h

theorem alphaCore_le_iff {K : Subgroup M} :
    alphaCore M ≤ K ↔ ∀ N : Subgroup M, N.Normal → IsPiSubgroup (alphaPrimes M) N → N ≤ K :=
  piCore_le_iff

theorem alphaCore_eq_closure (M : Type*) [Group M] [Finite M] :
    alphaCore M =
      Subgroup.closure {x | ∃ N : Subgroup M, N.Normal ∧ IsPiSubgroup (alphaPrimes M) N ∧ x ∈ N} :=
  piCore_eq_closure _ _

instance alphaCore_characteristic (M : Type*) [Group M] [Finite M] :
    (alphaCore M).Characteristic := by
  rw [alphaCore_eq_piCore]; infer_instance

theorem alphaCore_normal (M : Type*) [Group M] [Finite M] : (alphaCore M).Normal :=
  Subgroup.normal_of_characteristic _

theorem isPiSubgroup_alphaCore (M : Type*) [Group M] [Finite M] :
    IsPiSubgroup (alphaPrimes M) (alphaCore M) := isPiSubgroup_piCore _ _

theorem primeFactors_natCard_alphaCore_subset (M : Type*) [Group M] [Finite M] :
    ((Nat.card (alphaCore M)).primeFactors : Set ℕ) ⊆ alphaPrimes M :=
  fun _ hp => isPiSubgroup_iff.1 (isPiSubgroup_alphaCore M) _ hp

theorem isGreatest_alphaCore (M : Type*) [Group M] [Finite M] :
    IsGreatest {N : Subgroup M | N.Normal ∧ IsPiSubgroup (alphaPrimes M) N} (alphaCore M) :=
  isGreatest_piCore _ _

theorem alphaCore_eq_bot_of_alphaPrimes_eq_empty (M : Type*) [Group M] [Finite M]
    (h : alphaPrimes M = ∅) : alphaCore M = ⊥ := by
  rw [alphaCore_eq_piCore, h, piCore_empty]

theorem alphaCore_eq_bot_of_subsingleton (M : Type*) [Group M] [Finite M] [Subsingleton M] :
    alphaCore M = ⊥ :=
  alphaCore_eq_bot_of_alphaPrimes_eq_empty M alphaPrimes_eq_empty_of_subsingleton

end

end CFSG.FeitThompson
