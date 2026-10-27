module

public import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
public import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
public import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {X : Subgroup G} {c n : G}
    (hc : c ∈ centralizer (X : Set G)) (hn : n ∈ normalizer (X : Set G)) :
    n⁻¹ * c * n ∈ centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hy : n * x * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
  have hcy := (Subgroup.mem_centralizer_iff.1 hc) _ hy
  calc x * (n⁻¹ * c * n) = n⁻¹ * ((n * x * n⁻¹) * c) * n := by group
    _ = n⁻¹ * (c * (n * x * n⁻¹)) * n := by rw [hcy]
    _ = (n⁻¹ * c * n) * x := by group

theorem exists_mem_inf_normalizer_mul_mem_centralizer [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {X : Subgroup G} (_hX : X ≠ ⊥)
    (hXp : IsPGroup p X) (hXM : X ≤ M) {n : G} (hn : n ∈ normalizer (X : Set G)) :
    ∃ m ∈ M ⊓ normalizer (X : Set G), ∃ c ∈ centralizer (X : Set G), n = m * c := by
  have hXn : X ≤ MulAut.conj n • M := by
    have h : X.map (MulAut.conj n) = X := Subgroup.mem_normalizer_iff_map_conj_eq.1 hn
    rw [conj_smul_eq_map_conj, ← h]
    exact Subgroup.map_mono hXM
  have hX1 : X ≤ MulAut.conj (1 : G) • M := by simpa using hXM
  obtain ⟨c, hc, hcn⟩ :=
    exists_mem_centralizer_conj_smul_of_mem_sigmaPrimes hna hodd hsolv hM hpM hXp hXn hX1
  rw [conj_smul_conj_smul] at hcn
  simp only [map_one, one_smul] at hcn
  have hcnM : c * n ∈ M := by
    rw [← normalizer_coe_eq_of_isCoatom hna hM]
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    rw [← conj_smul_eq_map_conj]
    exact hcn
  exact ⟨c * n, ⟨hcnM, mul_mem (centralizer_le_normalizer _ hc) hn⟩,
    n⁻¹ * c⁻¹ * n, conj_mem_centralizer_of_mem_normalizer (inv_mem hc) hn, by group⟩

theorem coe_normalizer_eq_mul_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXp : IsPGroup p X) (hXM : X ≤ M) :
    (normalizer (X : Set G) : Set G)
      = (↑(M ⊓ normalizer (X : Set G)) : Set G) * (centralizer (X : Set G) : Set G) := by
  apply Set.eq_of_subset_of_subset
  · intro n hn
    obtain ⟨m, hm, c, hc, rfl⟩ :=
      exists_mem_inf_normalizer_mul_mem_centralizer hna hodd hsolv hM hpM hX hXp hXM hn
    exact Set.mul_mem_mul hm hc
  · rintro x ⟨m, hm, c, hc, rfl⟩
    exact mul_mem (inf_le_right (a := M) hm) (centralizer_le_normalizer _ hc)

theorem normalizer_eq_sup_centralizer_of_mem_sigmaPrimes [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXp : IsPGroup p X) (hXM : X ≤ M) :
    normalizer (X : Set G) = (M ⊓ normalizer (X : Set G)) ⊔ centralizer (X : Set G) := by
  refine le_antisymm (fun n hn => ?_) (sup_le inf_le_right (centralizer_le_normalizer _))
  obtain ⟨m, hm, c, hc, rfl⟩ :=
    exists_mem_inf_normalizer_mul_mem_centralizer hna hodd hsolv hM hpM hX hXp hXM hn
  exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hc)

end

end CFSG.FeitThompson
