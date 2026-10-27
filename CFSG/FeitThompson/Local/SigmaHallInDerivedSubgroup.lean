module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.OddOrder.SigmaSylowInDerived
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Representations.DadeSignalizersCanonicalNormalHall

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

omit [Finite G] in
private theorem map_subtype_commutator (L : Subgroup G) :
    (_root_.commutator ↥L).map L.subtype = ⁅L, L⁆ := by
  rw [commutator_eq_subgroupOf_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left]
  exact Subgroup.commutator_le.2 fun x hx y hy =>
    L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)

theorem not_dvd_index_commutator_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) :
    ¬ p ∣ (_root_.commutator ↥M).index := by
  have := Fact.mk (prime_of_mem_sigmaPrimes hpM)
  set S : Sylow p ↥M := default with hSdef
  have hS : (S : Subgroup ↥M) ≤ _root_.commutator ↥M := by
    have h := sylow_map_subtype_le_commutator_of_mem_sigmaPrimes hna hodd hsolv hM hpM S
    rw [commutator_eq_subgroupOf_commutator]
    have h2 := Subgroup.comap_mono (f := M.subtype) h
    rwa [Subgroup.comap_map_eq_self_of_injective M.subtype_injective] at h2
  exact fun hdvd => S.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hS))

theorem isPiNumber_compl_index_commutator_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M) :
    IsPiNumber (sigmaPrimes M)ᶜ (_root_.commutator ↥M).index :=
  isPiNumber_compl_iff.2 fun _ hq hq' =>
    not_dvd_index_commutator_of_mem_sigmaPrimes hna hodd hsolv hM hq'
      (Nat.dvd_of_mem_primeFactors hq)

theorem le_commutator_of_isPiSubgroup_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M)
    {T : Subgroup ↥M} (hT : IsPiSubgroup (sigmaPrimes M) T) : T ≤ _root_.commutator ↥M :=
  le_of_coprime_natCard_index
    ((isPiSubgroup_iff_isPiNumber.1 hT).coprime_of_compl
      (isPiNumber_compl_index_commutator_sigmaPrimes hna hodd hsolv hM)
      Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite)

theorem le_commutator_of_isHallSubgroup_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M)
    {T : Subgroup ↥M} (hT : IsHallSubgroup (sigmaPrimes M) T) : T ≤ _root_.commutator ↥M :=
  le_commutator_of_isPiSubgroup_sigmaPrimes hna hodd hsolv hM hT.isPiSubgroup

theorem le_commutator_of_isHallSubgroup_sigmaPrimes_subgroupOf [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M)
    {T : Subgroup G} (hTM : T ≤ M) (hT : IsHallSubgroup (sigmaPrimes M) (T.subgroupOf M)) :
    T ≤ ⁅M, M⁆ := by
  have h := le_commutator_of_isHallSubgroup_sigmaPrimes hna hodd hsolv hM hT
  have h2 := Subgroup.map_mono (f := M.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hTM, map_subtype_commutator] at h2

theorem le_commutator_of_isHallSubgroup_alphaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M)
    {J : Subgroup ↥M} (hJ : IsHallSubgroup (alphaPrimes ↥M) J) : J ≤ _root_.commutator ↥M :=
  le_commutator_of_isPiSubgroup_sigmaPrimes hna hodd hsolv hM
    (hJ.isPiSubgroup.mono (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM))

theorem le_commutator_of_isHallSubgroup_alphaPrimes_subgroupOf [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M)
    {J : Subgroup G} (hJM : J ≤ M) (hJ : IsHallSubgroup (alphaPrimes ↥M) (J.subgroupOf M)) :
    J ≤ ⁅M, M⁆ := by
  have h := le_commutator_of_isHallSubgroup_alphaPrimes hna hodd hsolv hM hJ
  have h2 := Subgroup.map_mono (f := M.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hJM, map_subtype_commutator] at h2

end

end CFSG.FeitThompson
