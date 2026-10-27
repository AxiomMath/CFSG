module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Local.PlaneRankThreeCentralizerUniqueness
import CFSG.FeitThompson.Local.OutsideSigmaSubgroupNonunique
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p q : ℕ} {M A : Subgroup G}

theorem elementaryAbelianPRank_centralizer_le_two_of_plane_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hq : q.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hAM : A ≤ M) (hpσ : p ∉ sigmaPrimes M)
    (hAea : IsElementaryAbelian p A) (hAcard : Nat.card ↥A = p ^ 2) :
    elementaryAbelianPRank q ↥(centralizer (A : Set G)) ≤ 2 := by
  by_contra hlt
  obtain ⟨N, hN⟩ :=
    exists_isUniqueMaximalOvergroup_of_plane_of_three_le_elementaryAbelianPRank_centralizer
      hp hq hna hodd hsolv hAea hAcard (by omega)
  refine not_isUniqueMaximalOvergroup_of_forall_prime_notMem_sigmaPrimes hna hodd hsolv hM hAM
    (fun r hr hdvd => ?_) hN
  rw [hAcard] at hdvd
  rw [(Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hdvd)]
  exact hpσ

theorem not_lt_of_isElementaryAbelian_of_plane_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hAM : A ≤ M) (hpσ : p ∉ sigmaPrimes M)
    (hAea : IsElementaryAbelian p A) (hAcard : Nat.card ↥A = p ^ 2)
    {E : Subgroup G} (hEea : IsElementaryAbelian p E) : ¬ A < E := by
  intro hAE
  have hcard : Nat.card ↥A < Nat.card ↥E :=
    lt_of_not_ge fun hge => hAE.ne (Subgroup.eq_of_le_of_card_ge hAE.le hge)
  obtain ⟨d, hd⟩ := hEea.exists_natCard_eq_pow hp
  have hd3 : 3 ≤ d := by
    rw [hAcard, hd, Nat.pow_lt_pow_iff_right hp.one_lt] at hcard
    omega
  have hrank : 3 ≤ elementaryAbelianPRank p ↥(centralizer (A : Set G)) :=
    hd3.trans (hEea.le_elementaryAbelianPRank hp hd (hEea.le_centralizer hAE.le))
  have := elementaryAbelianPRank_centralizer_le_two_of_plane_of_notMem_sigmaPrimes
    hp hp hna hodd hsolv hM hAM hpσ hAea hAcard
  omega

theorem maximal_isElementaryAbelian_of_plane_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hAM : A ≤ M) (hpσ : p ∉ sigmaPrimes M)
    (hAea : IsElementaryAbelian p A) (hAcard : Nat.card ↥A = p ^ 2) :
    Maximal (IsElementaryAbelian p) A :=
  ⟨hAea, fun E hEea hAEle => by
    by_contra hEA
    exact not_lt_of_isElementaryAbelian_of_plane_of_notMem_sigmaPrimes hp hna hodd hsolv hM hAM hpσ
      hAea hAcard hEea (lt_of_le_not_ge hAEle hEA)⟩

theorem eq_of_isElementaryAbelian_of_plane_of_notMem_sigmaPrimes
    [Finite G] [IsSimpleGroup G] (hp : p.Prime) (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hAM : A ≤ M) (hpσ : p ∉ sigmaPrimes M)
    (hAea : IsElementaryAbelian p A) (hAcard : Nat.card ↥A = p ^ 2)
    {E : Subgroup G} (hEea : IsElementaryAbelian p E) (hAE : A ≤ E) : E = A :=
  (maximal_isElementaryAbelian_of_plane_of_notMem_sigmaPrimes hp hna hodd hsolv hM hAM hpσ hAea
    hAcard).eq_of_ge hEea hAE

end

end CFSG.FeitThompson
