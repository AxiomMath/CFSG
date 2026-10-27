module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.KappaPrimes
public import CFSG.FeitThompson.Definitions.TauTwoPrimes
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {M X : Subgroup G} {q : ℕ}

theorem mem_tauTwoPrimes_of_dvd_natCard [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hXM : X ≤ M)
    (hX : ∀ r ∈ (Nat.card X).primeFactors, r ∉ sigmaPrimes M ∪ kappaPrimes M)
    (hC : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥)
    (hq : q.Prime) (hqX : q ∣ Nat.card X) : q ∈ tauTwoPrimes M := by
  have := Fact.mk hq
  have hqmem : q ∈ (Nat.card X).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hq, hqX, Nat.card_pos.ne'⟩
  have hqσ : q ∉ sigmaPrimes M := fun h => hX q hqmem (Or.inl h)
  have hqκ : q ∉ kappaPrimes M := fun h => hX q hqmem (Or.inr h)
  have hqM : q ∣ Nat.card M := hqX.trans (Subgroup.card_dvd_of_le hXM)
  have hle2 : elementaryAbelianPRank q ↥M ≤ 2 := by
    by_contra h
    exact hqσ (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM (mem_alphaPrimes.2 ⟨hq, by omega⟩))
  have hge1 : 1 ≤ elementaryAbelianPRank q ↥M := (one_le_elementaryAbelianPRank_iff hq).2 hqM
  refine mem_tauTwoPrimes_iff.2 ⟨hq, hqσ, ?_⟩
  by_contra hne
  have hr1 : elementaryAbelianPRank q ↥M = 1 := by omega
  have hqodd : Odd q := by
    refine hq.odd_of_ne_two fun h => ?_
    subst h
    have h2 : (2 : ℕ) ∣ Nat.card G := hqM.trans (Subgroup.card_subgroup_dvd_card M)
    have h3 : Nat.card G % 2 = 1 := Nat.odd_iff.1 hodd
    omega
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) q hqX
  have hxX : (x₀ : G) ∈ X := x₀.2
  have hxorder : orderOf (x₀ : G) = q := (Subgroup.orderOf_coe x₀).trans hx₀
  have hx1 : (x₀ : G) ≠ 1 := fun h => hq.ne_one (by rw [← hxorder, h, orderOf_one])
  set xM : ↥M := ⟨(x₀ : G), hXM hxX⟩ with hxM
  have hordM : orderOf xM = q := (Subgroup.orderOf_coe xM).symm.trans hxorder
  have hpg : IsPGroup q (Subgroup.zpowers xM) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hordM, pow_one])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hxS : xM ∈ (S : Subgroup ↥M) := hS (Subgroup.mem_zpowers xM)
  have hcyc : IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
    rw [isCyclic_map_subtype_iff]
    by_contra hnc
    have h2 := two_le_elementaryAbelianPRank_of_not_isCyclic hq hqodd S.isPGroup' hnc
    have h3 := elementaryAbelianPRank_subgroup_le (X := ↥M) hq.one_lt (S : Subgroup ↥M)
    omega
  have hcent : sigmaCore M ⊓ centralizer ({(x₀ : G)} : Set G) ≠ ⊥ :=
    ne_bot_of_le_ne_bot hC
      (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxX)))
  exact hqκ (mem_kappaPrimes_iff.2 ⟨hq, hqM, hqσ, S, hcyc,
    (x₀ : G), Subgroup.mem_map_of_mem _ hxS, hx1, hcent⟩)

theorem primeFactors_subset_tauTwoPrimes [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hXM : X ≤ M)
    (hX : ∀ r ∈ (Nat.card X).primeFactors, r ∉ sigmaPrimes M ∪ kappaPrimes M)
    (hC : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥) :
    ↑(Nat.card X).primeFactors ⊆ tauTwoPrimes M := fun _ hr =>
  mem_tauTwoPrimes_of_dvd_natCard hna hodd hsolv hM hXM hX hC
    (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)

theorem primeFactors_subset_tauTwoPrimes_of_isPiSubgroup [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hXM : X ≤ M)
    (hX : IsPiSubgroup (sigmaPrimes M ∪ kappaPrimes M)ᶜ X)
    (hC : sigmaCore M ⊓ centralizer (X : Set G) ≠ ⊥) :
    ↑(Nat.card X).primeFactors ⊆ tauTwoPrimes M :=
  primeFactors_subset_tauTwoPrimes hna hodd hsolv hM hXM (isPiSubgroup_iff.1 hX) hC

end

end CFSG.FeitThompson
