module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.BurnsideNormalPComplement
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem commutator_eq_closure_conj_comm (H K : Subgroup G) :
    ⁅H, K⁆ = closure {g | ∃ x ∈ H, ∃ y ∈ K, x⁻¹ * y⁻¹ * x * y = g} := by
  rw [Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, by group⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x⁻¹, H.inv_mem hx, y⁻¹, K.inv_mem hy, by group⟩

theorem commutator_normalizer_le (P : Subgroup G) : ⁅P, normalizer (P : Set G)⁆ ≤ P :=
  le_normalizer_iff_commutator_le_left.mp le_rfl

theorem normalizer_le_normalizer_commutator (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer ((⁅P, normalizer (P : Set G)⁆ : Subgroup G) : Set G) := by
  intro g hg
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_commutator, mem_normalizer_iff_map_conj_eq.mp hg,
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)]

theorem normal_commutator_normalizer_subgroupOf (P : Subgroup G) :
    ((⁅P, normalizer (P : Set G)⁆ : Subgroup G).subgroupOf (normalizer (P : Set G))).Normal :=
  (normal_subgroupOf_iff_le_normalizer
      ((commutator_normalizer_le P).trans le_normalizer)).mpr
    (normalizer_le_normalizer_commutator P)

theorem commutator_normalizer_ne_bot [Finite G] [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hp : p.Prime) {P : Subgroup G} (hP : P ≠ ⊥)
    (hPsylow : Nat.card P = p ^ (Nat.card G).factorization p) :
    ⁅P, normalizer (P : Set G)⁆ ≠ ⊥ := by
  have := Fact.mk hp
  intro h0
  have hcent : P ≤ centralizer ((normalizer (P : Set G) : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp h0
  have hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n :=
    fun n hn x hx => mem_centralizer_iff.mp (hcent hx) n hn
  obtain ⟨K, hKnormal, -, hKindex, -, -⟩ :=
    exists_normal_pComplement_of_normalizer_comm hPsylow hcomm
  rcases (haveI := hKnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal K) with rfl | rfl
  ·
    rw [index_bot] at hKindex
    exact (lt_top_of_isPGroup hG hp hP (IsPGroup.of_card hPsylow)).ne
      (P.eq_top_of_card_eq hKindex.symm)
  ·
    rw [index_top] at hKindex
    exact hP (card_eq_one.mp hKindex.symm)

theorem commutator_normalizer_ne_bot_and_le_and_normal [Finite G] (_hodd : Odd (Nat.card G))
    (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hp : p.Prime) {P : Subgroup G}
    (hP : P ≠ ⊥) (hPsylow : Nat.card P = p ^ (Nat.card G).factorization p) :
    ⁅P, normalizer (P : Set G)⁆ ≠ ⊥ ∧ ⁅P, normalizer (P : Set G)⁆ ≤ P ∧
      ((⁅P, normalizer (P : Set G)⁆ : Subgroup G).subgroupOf (normalizer (P : Set G))).Normal :=
  have := hsimple
  ⟨commutator_normalizer_ne_bot hG hp hP hPsylow, commutator_normalizer_le P,
    normal_commutator_normalizer_subgroupOf P⟩

theorem sylow_commutator_normalizer_ne_bot_and_le_and_normal [Finite G] [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hp : p.Prime) (P : Sylow p G) (hP : (P : Subgroup G) ≠ ⊥) :
    ⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ ≠ ⊥ ∧
      ⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ ≤ (P : Subgroup G) ∧
      ((⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ : Subgroup G).subgroupOf
        (normalizer ((P : Subgroup G) : Set G))).Normal :=
  have := Fact.mk hp
  ⟨commutator_normalizer_ne_bot hG hp hP P.card_eq_multiplicity,
    commutator_normalizer_le _, normal_commutator_normalizer_subgroupOf _⟩

end CFSG.FeitThompson
