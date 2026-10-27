module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.FocalSubgroupTheorem
import CFSG.FeitThompson.OddOrder.SigmaElementFusionControlled
import CFSG.FeitThompson.OddOrder.NonabelianSimplePerfect
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
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
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem le_commutator_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {P : Subgroup G} (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) :
    P ≤ ⁅M, M⁆ := by
  have := Fact.mk (prime_of_mem_sigmaPrimes hpM)
  have hPG : Nat.card P = p ^ (Nat.card G).factorization p :=
    natCard_eq_pow_factorization_of_mem_sigmaPrimes hpM hPM hPcard
  have hPp : IsPGroup p P := IsPGroup.of_card hPG
  have hfocal : focalSubgroup P = P := by
    rw [← inf_commutator_eq_focalSubgroup hPG, commutator_eq_top_of_not_isMulCommutative hna,
      inf_top_eq]
  rw [← hfocal, focalSubgroup_def, closure_le]
  rintro g ⟨hgP, x, hxP, u, rfl⟩
  have hxM : x ∈ M := hPM hxP
  have horder : ∃ k, orderOf x⁻¹ = p ^ k := by
    rw [orderOf_inv]
    obtain ⟨k, hk⟩ := hPp.exists_orderOf_eq_pow ⟨x, hxP⟩
    exact ⟨k, by simpa using hk⟩
  have hconj : (u⁻¹)⁻¹ * x⁻¹ * u⁻¹ ∈ M := by
    have h : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by rw [commutatorElement_def]; group
    rw [inv_inv, h]
    exact M.mul_mem (M.inv_mem hxM) (hPM hgP)
  obtain ⟨m, hm, hmeq⟩ := exists_mem_conj_eq_of_mem_sigmaPrimes hna hodd hsolv hM hpM
    (M.inv_mem hxM) horder hconj
  rw [inv_inv] at hmeq
  have hrw : ⁅x, u⁆ = ⁅x, m⁻¹⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      _ = x * (m⁻¹ * x⁻¹ * m) := by rw [hmeq]
      _ = x * m⁻¹ * x⁻¹ * m⁻¹⁻¹ := by group
  rw [hrw]
  exact commutator_mem_commutator hxM (M.inv_mem hm)

theorem sylow_map_subtype_le_commutator_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) (S : Sylow p M) :
    (S : Subgroup M).map M.subtype ≤ ⁅M, M⁆ := by
  have hp := prime_of_mem_sigmaPrimes hpM
  have := Fact.mk hp
  obtain ⟨-, hcard⟩ :=
    (exists_sylow_map_subtype_eq_iff hp (P := (S : Subgroup M).map M.subtype)).1 ⟨S, rfl⟩
  exact le_commutator_of_mem_sigmaPrimes hna hodd hsolv hM hpM (map_subtype_le _) hcard

theorem subgroupOf_le_commutator_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {P : Subgroup G} (hPM : P ≤ M)
    (hPcard : Nat.card P = p ^ (Nat.card M).factorization p) :
    P.subgroupOf M ≤ _root_.commutator M := by
  rw [commutator_eq_subgroupOf_commutator]
  exact comap_mono (le_commutator_of_mem_sigmaPrimes hna hodd hsolv hM hpM hPM hPcard)

end

end CFSG.FeitThompson
