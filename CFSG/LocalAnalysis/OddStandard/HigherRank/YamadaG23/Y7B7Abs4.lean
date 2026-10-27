module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs1
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private def y7b_stab (K : Subgroup G) (t : G) : Subgroup G where
  carrier := {x | x ∈ normalizer (K : Set G) ∧ ⁅x, t⁆ ∈ K}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    simp [commutatorElement_def]
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxN, hxC⟩ := hx
    obtain ⟨hyN, hyC⟩ := hy
    refine ⟨Subgroup.mul_mem _ hxN hyN, ?_⟩
    have hxy : ⁅x * y, t⁆ = x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆ := by
      simp only [commutatorElement_def]; group
    rw [hxy]
    exact K.mul_mem ((Subgroup.mem_set_normalizer_iff.mp hxN) ⁅y, t⁆ |>.mp hyC) hxC
  inv_mem' := by
    intro x hx
    obtain ⟨hxN, hxC⟩ := hx
    refine ⟨Subgroup.inv_mem _ hxN, ?_⟩
    have hxi : ⁅x⁻¹, t⁆ = x⁻¹ * ⁅x, t⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [hxi]
    simpa using (Subgroup.mem_set_normalizer_iff.mp (Subgroup.inv_mem _ hxN) ⁅x, t⁆⁻¹
      |>.mp (K.inv_mem hxC))

theorem y7b_stab_sup {K C M : Subgroup G} {t : G}
    (hC : ∀ x ∈ C, x ∈ normalizer (K : Set G) ∧ ⁅x, t⁆ ∈ K)
    (hM : ∀ x ∈ M, x ∈ normalizer (K : Set G) ∧ ⁅x, t⁆ ∈ K) :
    ∀ x ∈ C ⊔ M, x ∈ normalizer (K : Set G) ∧ ⁅x, t⁆ ∈ K := by
  have hsub : C ⊔ M ≤ y7b_stab K t :=
    sup_le (fun x hx => hC x hx) (fun x hx => hM x hx)
  intro x hx
  exact hsub hx

end CFSG.OddStandard.HigherRank.YamadaG23
