module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.NarrowPrimeLengthQuotientPrimeBound
import CFSG.FeitThompson.Local.MinimalSimpleProperSubgroupPLengthOne
import CFSG.FeitThompson.Local.LowRankSmallestPrimeHallReduction
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_isPNarrow_of_notMem_betaPrimes {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hpX : p ∣ Nat.card X) (h : p ∉ betaPrimes X) :
    ∃ P : Sylow p X, IsPNarrow p ↥(P : Subgroup X) := by
  by_contra hcon
  exact h (mem_betaPrimes_iff.2
    ⟨Nat.mem_primeFactors.2 ⟨hp, hpX, Nat.card_pos.ne'⟩, by simpa using hcon⟩)

theorem prime_le_of_dvd_natCard_quotient_pComplCore_of_ne_top [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M : Subgroup G} (hM : M ≠ ⊤)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hpbeta : p ∉ betaPrimes ↥M)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ Nat.card (↥M ⧸ pComplCore p ↥M)) : q ≤ p := by
  have := Fact.mk hp
  have hMsolv : Group.IsSolvable ↥M := hsolv M hM
  by_cases hpM : p ∣ Nat.card ↥M
  · obtain ⟨P, hPnarrow⟩ := exists_sylow_isPNarrow_of_notMem_betaPrimes hp hpM hpbeta
    exact prime_le_of_dvd_natCard_quotient_pComplCore hpodd
      (hodd.of_dvd_nat M.card_subgroup_dvd_card) P.card_eq_multiplicity hPnarrow
      (hasPLengthLeOne_iff_card.1 (hasPLengthLeOne_of_ne_top hna hodd hsolv hM hp)) hq hqM
  · rw [pComplCore_eq_top_of_not_dvd hpM, ← Subgroup.index_eq_card, Subgroup.index_top] at hqM
    exact absurd (Nat.dvd_one.1 hqM) hq.ne_one

theorem forall_mem_primeFactors_natCard_quotient_pComplCore_le_of_ne_top [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) {M : Subgroup G} (hM : M ≠ ⊤)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hpbeta : p ∉ betaPrimes ↥M) :
    ∀ q ∈ (Nat.card (↥M ⧸ pComplCore p ↥M)).primeFactors, q ≤ p := fun _ hmem =>
  prime_le_of_dvd_natCard_quotient_pComplCore_of_ne_top hna hodd hsolv hM hp hpodd hpbeta
    (Nat.prime_of_mem_primeFactors hmem) (Nat.dvd_of_mem_primeFactors hmem)

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson

universe u

theorem FTS_beta_prime_quotient_largest_prime :
    Statements.FTS_beta_prime_quotient_largest_prime.{u} := by
  intro G _ _ hG M hM p hp hpodd hpbeta
  have := hG.simple
  exact ⟨pComplCore_normal p ↥M,
    forall_mem_primeFactors_natCard_quotient_pComplCore_le_of_ne_top hG.nonabelian hG.odd
      hG.solvable hM.1 hp hpodd hpbeta⟩

end

end CFSG.FeitThompson.Proofs

