module

public import CFSG.GroupTheory.LocalCores.Components
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem generalized_fitting_product [Finite G] :
    ((generalizedFitting G : Subgroup G) : Set G) =
        (fittingSubgroup G : Set G) * (layer G : Set G) ∧
      ∃ μ : (fittingSubgroup G) × (layer G) →* generalizedFitting G,
        (∀ x y, (μ (x, y) : G) = x * y) ∧ Function.Surjective μ ∧
        (μ.ker : Set ((fittingSubgroup G) × (layer G))) =
          {p | ∃ z ∈ fittingSubgroup G ⊓ layer G, (p.1 : G) = z ∧ (p.2 : G) = z⁻¹} := by
  have hcomm : ∀ x ∈ fittingSubgroup G, ∀ y ∈ layer G, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.LocalCores.fitting_layer_commute (G := G))
    exact (mem_centralizer_iff.1 (hle hx) y hy).symm
  have hset : ((generalizedFitting G : Subgroup G) : Set G) =
      (fittingSubgroup G : Set G) * (layer G : Set G) := by
    refine Subgroup.coe_mul_of_left_le_normalizer_right _ _ ?_
    refine le_trans ?_ (centralizer_le_normalizer _)
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  let ν : (fittingSubgroup G) × (layer G) →* G :=
    MonoidHom.noncommCoprod (fittingSubgroup G).subtype (layer G).subtype
      fun x y => hcomm x x.2 y y.2
  have hν_apply : ∀ p, ν p = (p.1 : G) * p.2 := fun p => rfl
  have hν : ∀ p, ν p ∈ generalizedFitting G := fun p => by
    rw [hν_apply]
    exact mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)
  refine ⟨hset, ν.codRestrict _ hν, fun x y => hν_apply (x, y), ?_, ?_⟩
  · rintro ⟨g, hg⟩
    have hg' : g ∈ (fittingSubgroup G : Set G) * (layer G : Set G) := by
      rw [← hset]; exact hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg'
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  · ext p
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_ofPred_eq]
    constructor
    · intro h
      have h' : (p.1 : G) * p.2 = 1 := congrArg Subtype.val h
      refine ⟨p.1, Subgroup.mem_inf.2 ⟨p.1.2, ?_⟩, rfl, eq_inv_of_mul_eq_one_right h'⟩
      rw [eq_inv_of_mul_eq_one_left h']
      exact inv_mem p.2.2
    · rintro ⟨z, -, h1, h2⟩
      apply Subtype.ext
      change (p.1 : G) * p.2 = 1
      rw [h1, h2, mul_inv_cancel]

end CFSG.LocalAnalysis.ComponentInitial
