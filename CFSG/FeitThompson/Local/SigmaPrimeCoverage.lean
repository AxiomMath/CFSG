module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem exists_isCoatom_mem_sigmaPrimes [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hp : p.Prime) (hdvd : p ∣ Nat.card G) :
    ∃ M : Subgroup G, IsCoatom M ∧ p ∈ sigmaPrimes M := by
  have := Fact.mk hp
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hn : (Nat.card G).factorization p ≠ 0 :=
    (hp.factorization_pos_of_dvd Nat.card_pos.ne' hdvd).ne'
  have hpP : p ∣ Nat.card (P : Subgroup G) := by
    rw [P.card_eq_multiplicity]; exact dvd_pow_self p hn
  have hPbot : (P : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hpP
    exact hp.ne_one (Nat.dvd_one.1 hpP)
  have hlt : normalizer ((P : Subgroup G) : Set G) < ⊤ :=
    normalizer_lt_top_of_isPGroup hG hp hPbot P.isPGroup'
  obtain ⟨M, hM, hNM⟩ := exists_isCoatom_ge_of_ne_top hlt.ne
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
  refine ⟨M, hM, mem_sigmaPrimes_iff.2 ⟨hp, hpP.trans (Subgroup.card_dvd_of_le hPM), ?_⟩⟩
  refine ⟨P.subtype hPM, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPM]
  exact hNM

theorem exists_maximal_subgroup_mem_sigmaPrimes (_hodd : Odd (Nat.card G))
    (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hp : p.Prime)
    (hdvd : p ∣ Nat.card G) :
    ∃ M : Subgroup G, (M ≠ ⊤ ∧ ∀ K : Subgroup G, ¬(M < K ∧ K < ⊤)) ∧ p ∈ sigmaPrimes M :=
  have := hsimple
  let ⟨M, hM, hp'⟩ := exists_isCoatom_mem_sigmaPrimes hG hp hdvd
  ⟨M, isCoatom_iff_ne_top_and_forall_not_lt_lt.1 hM, hp'⟩

theorem primeFactors_subset_iUnion_sigmaPrimes [IsSimpleGroup G] (hG : ¬ IsMulCommutative G) :
    ↑(Nat.card G).primeFactors ⊆ ⋃ M ∈ {M : Subgroup G | IsCoatom M}, sigmaPrimes M := by
  intro p hp
  rw [Finset.mem_coe, Nat.mem_primeFactors] at hp
  obtain ⟨M, hM, hpM⟩ := exists_isCoatom_mem_sigmaPrimes hG hp.1 hp.2.1
  exact Set.mem_biUnion hM hpM

end

end CFSG.FeitThompson
