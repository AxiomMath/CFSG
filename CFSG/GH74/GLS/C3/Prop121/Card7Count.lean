module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup

theorem double_count {G : Type*} [Group G] [Finite G] (N : Subgroup G) (x y : G)
    (R : G → G → Prop)
    (hR : ∀ c ∈ N, ∀ a b : G, R (c * a * c⁻¹) (c * b * c⁻¹) ↔ R a b) :
    Nat.card {a : G // ∃ c ∈ N, c * x * c⁻¹ = a} *
        Nat.card {b : G // (∃ c ∈ N, c * y * c⁻¹ = b) ∧ R x b} =
      Nat.card {b : G // ∃ c ∈ N, c * y * c⁻¹ = b} *
        Nat.card {a : G // (∃ c ∈ N, c * x * c⁻¹ = a) ∧ R a y} := by
  classical
  have := Fintype.ofFinite G
  set Af : Finset G := Finset.univ.filter (fun a => ∃ c ∈ N, c * x * c⁻¹ = a) with hAf
  set Bf : Finset G := Finset.univ.filter (fun b => ∃ c ∈ N, c * y * c⁻¹ = b) with hBf
  have hbip := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Af) (t := Bf) R
  have hdegA : ∀ a ∈ Af, (Bf.bipartiteAbove R a).card = (Bf.bipartiteAbove R x).card := by
    intro a ha
    obtain ⟨c0, hc0, rfl⟩ : ∃ c ∈ N, c * x * c⁻¹ = a := by simpa [hAf] using ha
    refine Finset.card_nbij' (fun b => c0⁻¹ * b * c0) (fun b => c0 * b * c0⁻¹) ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, hBf,
        Finset.bipartiteAbove] at hb ⊢
      obtain ⟨⟨c1, hc1, rfl⟩, hR1⟩ := hb
      refine ⟨⟨c0⁻¹ * c1, N.mul_mem (N.inv_mem hc0) hc1, by group⟩, ?_⟩
      have := (hR c0⁻¹ (N.inv_mem hc0) (c0 * x * c0⁻¹) (c1 * y * c1⁻¹)).2 hR1
      simpa [mul_assoc] using this
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, hBf,
        Finset.bipartiteAbove] at hb ⊢
      obtain ⟨⟨c1, hc1, rfl⟩, hR1⟩ := hb
      refine ⟨⟨c0 * c1, N.mul_mem hc0 hc1, by group⟩, ?_⟩
      have := (hR c0 hc0 x (c1 * y * c1⁻¹)).2 hR1
      simpa [mul_assoc] using this
    · intro b _; group
    · intro b _; group
  have hdegB : ∀ b ∈ Bf, (Af.bipartiteBelow R b).card = (Af.bipartiteBelow R y).card := by
    intro b hb
    obtain ⟨c0, hc0, rfl⟩ : ∃ c ∈ N, c * y * c⁻¹ = b := by simpa [hBf] using hb
    refine Finset.card_nbij' (fun a => c0⁻¹ * a * c0) (fun a => c0 * a * c0⁻¹) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, hAf,
        Finset.bipartiteBelow] at ha ⊢
      obtain ⟨⟨c1, hc1, rfl⟩, hR1⟩ := ha
      refine ⟨⟨c0⁻¹ * c1, N.mul_mem (N.inv_mem hc0) hc1, by group⟩, ?_⟩
      have := (hR c0⁻¹ (N.inv_mem hc0) (c1 * x * c1⁻¹) (c0 * y * c0⁻¹)).2 hR1
      simpa [mul_assoc] using this
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, hAf,
        Finset.bipartiteBelow] at ha ⊢
      obtain ⟨⟨c1, hc1, rfl⟩, hR1⟩ := ha
      refine ⟨⟨c0 * c1, N.mul_mem hc0 hc1, by group⟩, ?_⟩
      have := (hR c0 hc0 (c1 * x * c1⁻¹) y).2 hR1
      simpa [mul_assoc] using this
    · intro a _; group
    · intro a _; group
  rw [Finset.sum_congr rfl hdegA, Finset.sum_congr rfl hdegB] at hbip
  simp only [Finset.sum_const, smul_eq_mul] at hbip
  have e1 : Nat.card {a : G // ∃ c ∈ N, c * x * c⁻¹ = a} = Af.card := by
    rw [hAf, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e2 : Nat.card {b : G // ∃ c ∈ N, c * y * c⁻¹ = b} = Bf.card := by
    rw [hBf, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e3 : Nat.card {b : G // (∃ c ∈ N, c * y * c⁻¹ = b) ∧ R x b} = (Bf.bipartiteAbove R x).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.bipartiteAbove, hBf, Finset.filter_filter]
  have e4 : Nat.card {a : G // (∃ c ∈ N, c * x * c⁻¹ = a) ∧ R a y} = (Af.bipartiteBelow R y).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.bipartiteBelow, hAf, Finset.filter_filter]
  rw [e1, e2, e3, e4]
  exact hbip

end CFSG.GH74.GLS.C3.Prop121.Card7
