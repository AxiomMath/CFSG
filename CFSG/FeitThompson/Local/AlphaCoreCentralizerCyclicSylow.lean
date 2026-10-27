module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.AlphaCentralizerUniqueOvergroup
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem exists_mem_orderOf_eq_isCyclic_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {M : Subgroup G} (hM : IsCoatom M) {q : ℕ} (hq : q.Prime) (hqs : q ∉ sigmaPrimes M)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQcard : Nat.card Q = q ^ (Nat.card M).factorization q)
    (hQ : Q ≠ ⊥) :
    ∃ x ∈ Q, orderOf x = q ∧ ∀ r : ℕ, r.Prime → ∀ P : Subgroup G,
      P ≤ (alphaCore ↥M).map M.subtype ⊓ centralizer ({x} : Set G) → IsPGroup r ↥P →
      IsCyclic ↥P := by
  obtain ⟨x, hxZ, hxo, hxlt, hxu⟩ :=
    exists_mem_inf_centralizer_orderOf_eq_of_notMem_sigmaPrimes hna hodd hsolv hM hq hqs hQM
      hQcard hQ
  have hxQ : x ∈ Q := (Subgroup.mem_inf.1 hxZ).1
  refine ⟨x, hxQ, hxo, fun r hr P hPle hPp => ?_⟩
  have := Fact.mk hr
  by_contra hnc
  obtain ⟨k, hk⟩ := hPp.exists_card_eq
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero, Nat.card_eq_one_iff_unique] at hk
      exact absurd (@isCyclic_of_subsingleton _ _ hk.1) hnc
    · exact h
  have hrdvd : r ∣ Nat.card ↥P := hk ▸ dvd_pow_self r (by omega)
  have hrodd : Odd r := hodd.of_dvd_nat (hrdvd.trans P.card_subgroup_dvd_card)
  have hrank : 2 ≤ elementaryAbelianPRank r ↥P :=
    two_le_elementaryAbelianPRank_of_not_isCyclic hr hrodd hPp hnc
  have hrank2 : 2 ≤ elementaryAbelianPRank r
      ↥((alphaCore ↥M).map M.subtype ⊓ centralizer ((zpowers x : Subgroup G) : Set G)) := by
    rw [centralizer_coe_zpowers]
    exact hrank.trans (elementaryAbelianPRank_le_of_le hr.one_lt hPle)
  have hxM : (zpowers x : Subgroup G) ≤ M := zpowers_le_of_mem (hQM hxQ)
  have hXα : ∀ p ∈ (Nat.card ↥(zpowers x : Subgroup G)).primeFactors, p ∉ alphaPrimes ↥M := by
    intro p hp
    rw [Nat.card_zpowers, hxo, hq.primeFactors, Finset.mem_singleton] at hp
    subst hp
    exact fun h => hqs (mem_sigmaPrimes_of_mem_alphaPrimes hna hodd hsolv hM h)
  have huniq :=
    isUniqueMaximalOvergroup_inf_centralizer_of_two_le_elementaryAbelianPRank_inf_alphaCore
      hna hodd hsolv hM hxM hXα hr hrank2
  refine hxu (huniq.mono (le_trans inf_le_right ?_) hxlt.ne)
  rw [centralizer_coe_zpowers]

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson

universe u

theorem FTS_alpha_core_prime_centralizer_choice :
    Statements.FTS_alpha_core_prime_centralizer_choice.{u} := by
  intro G _ _ hG M Q hM q hq hqs hQ hQsyl
  have := hG.simple
  obtain ⟨hQM, hQcard⟩ := hQsyl
  obtain ⟨x, hxQ, hxo, hx⟩ :=
    exists_mem_orderOf_eq_isCyclic_of_notMem_sigmaPrimes hG.nonabelian hG.odd hG.solvable hM hq
      hqs hQM hQcard hQ
  refine ⟨x, hxQ, hxo, fun r hr P hP => ?_⟩
  obtain ⟨hPle, hPcard⟩ := hP
  rw [CFSG.FeitThompson.Prep06.alphaCoreIn_eq] at hPle
  exact hx r hr P hPle (IsPGroup.of_card hPcard)

end

end CFSG.FeitThompson.Proofs
