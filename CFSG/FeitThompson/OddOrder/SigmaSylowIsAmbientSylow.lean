module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem natCard_eq_pow_factorization_of_mem_sigmaPrimes (hpM : p ∈ sigmaPrimes M) {P : Subgroup G}
    (hPM : P ≤ M) (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) :
    Nat.card P = p ^ (Nat.card G).factorization p := by
  have hp := prime_of_mem_sigmaPrimes hpM
  obtain ⟨S, hS⟩ := (exists_sylow_map_subtype_eq_iff hp (P := P)).2 ⟨hPM, hPcard⟩
  have hN := ((mem_sigmaPrimes_iff_forall hp).1 hpM).2 S
  rw [hS] at hN
  exact natCard_eq_pow_factorization_of_normalizer_le hp hPcard hN

theorem natCard_map_subtype_eq_pow_factorization (hpM : p ∈ sigmaPrimes M) (S : Sylow p M) :
    Nat.card ((S : Subgroup M).map M.subtype : Subgroup G) = p ^ (Nat.card G).factorization p := by
  have hp := prime_of_mem_sigmaPrimes hpM
  obtain ⟨-, hcard⟩ :=
    (exists_sylow_map_subtype_eq_iff hp (P := (S : Subgroup M).map M.subtype)).1 ⟨S, rfl⟩
  exact natCard_eq_pow_factorization_of_mem_sigmaPrimes hpM (Subgroup.map_subtype_le _) hcard

theorem exists_sylow_coe_eq_map_subtype (hpM : p ∈ sigmaPrimes M) (S : Sylow p M) :
    ∃ T : Sylow p G, (T : Subgroup G) = (S : Subgroup M).map M.subtype :=
  have := Fact.mk (prime_of_mem_sigmaPrimes hpM)
  ⟨Sylow.ofCard _ (natCard_map_subtype_eq_pow_factorization hpM S), Sylow.coe_ofCard _ _⟩

theorem factorization_eq_of_mem_sigmaPrimes (hpM : p ∈ sigmaPrimes M) :
    (Nat.card M).factorization p = (Nat.card G).factorization p := by
  have hp := prime_of_mem_sigmaPrimes hpM
  have := Fact.mk hp
  have hcard := ((exists_sylow_map_subtype_eq_iff hp
    (P := ((default : Sylow p M) : Subgroup M).map M.subtype)).1 ⟨default, rfl⟩).2
  exact Nat.pow_right_injective hp.two_le
    (hcard.symm.trans (natCard_map_subtype_eq_pow_factorization hpM default))

theorem sigmaSylow_isSylow_of_ambient_hypotheses (_hsimple : IsSimpleGroup G)
    (_hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (_hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K) (_hM : IsCoatom M)
    (hpM : p ∈ sigmaPrimes M) {P : Subgroup G} (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) :
    Nat.card P = p ^ (Nat.card G).factorization p ∧ ∃ T : Sylow p G, (T : Subgroup G) = P := by
  have hcard := natCard_eq_pow_factorization_of_mem_sigmaPrimes hpM hPM hPcard
  have := Fact.mk (prime_of_mem_sigmaPrimes hpM)
  exact ⟨hcard, Sylow.ofCard P hcard, Sylow.coe_ofCard _ _⟩

end

end CFSG.FeitThompson
