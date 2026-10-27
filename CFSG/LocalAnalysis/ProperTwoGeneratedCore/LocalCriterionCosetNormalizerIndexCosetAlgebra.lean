module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open scoped Pointwise

universe v

variable {G : Type v} [Group G]

theorem involution_translate_square_eq_subgroup (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    ((fun x : G => u * x) '' (U : Set G)) *
        ((fun x : G => u * x) '' (U : Set G)) = (U : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨w, hw, rfl⟩ := hb
    have hmul : (u * y) * (u * w) = y * w := by
      calc
        _ = (u * (y * u)) * w := by simp only [mul_assoc]
        _ = (u * (u * y)) * w :=
          congrArg (fun a : G => (u * a) * w) (hcentral y hy).eq.symm
        _ = y * w := by rw [← mul_assoc u u y, hu, one_mul]
    rw [hmul]
    exact U.mul_mem hy hw
  · intro hx
    apply Set.mem_mul.mpr
    refine ⟨u, ⟨1, U.one_mem, mul_one u⟩, u * x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← mul_assoc, hu, one_mul]

theorem closure_translate_eq_sup (U : Subgroup G) (u : G) :
    Subgroup.closure ((fun x : G => u * x) '' (U : Set G)) =
      Subgroup.closure ({u} : Set G) ⊔ U := by
  let Delta : Set G := (fun x : G => u * x) '' (U : Set G)
  have huDelta : u ∈ Subgroup.closure Delta :=
    Subgroup.subset_closure ⟨1, U.one_mem, mul_one u⟩
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨y, hy, rfl⟩
    apply (Subgroup.closure ({u} : Set G) ⊔ U).mul_mem
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_singleton u))
    · exact Subgroup.mem_sup_right hy
  · apply sup_le
    · apply (Subgroup.closure_le _).mpr
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact huDelta
    · intro x hx
      have hux : u * x ∈ Subgroup.closure Delta := Subgroup.subset_closure ⟨x, hx, rfl⟩
      have h := (Subgroup.closure Delta).mul_mem
        ((Subgroup.closure Delta).inv_mem huDelta) hux
      simpa only [inv_mul_cancel_left] using h

theorem set_normalizer_le_square_normalizer (Delta : Set G) :
    Subgroup.normalizer Delta ≤ Subgroup.normalizer (Delta * Delta) := by
  have hforward (g : G) (hg : g ∈ Subgroup.normalizer Delta) (x : G)
      (hx : x ∈ Delta * Delta) : g * x * g⁻¹ ∈ Delta * Delta := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    have hga : g * a * g⁻¹ ∈ Delta := hg a |>.mp ha
    have hgb : g * b * g⁻¹ ∈ Delta := hg b |>.mp hb
    apply Set.mem_mul.mpr
    refine ⟨g * a * g⁻¹, hga, g * b * g⁻¹, hgb, ?_⟩
    simp only [mul_assoc, inv_mul_cancel_left]
  intro g hg
  change ∀ x, x ∈ Delta * Delta ↔ g * x * g⁻¹ ∈ Delta * Delta
  intro x
  constructor
  · exact hforward g hg x
  · intro hx
    have h := hforward g⁻¹ ((Subgroup.normalizer Delta).inv_mem hg)
      (g * x * g⁻¹) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

theorem involution_translate_normalizer_le_unit_normalizer (U : Subgroup G) (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) ≤
      Subgroup.normalizer (U : Set G) := by
  have h := set_normalizer_le_square_normalizer
    ((fun x : G => u * x) '' (U : Set G))
  rw [involution_translate_square_eq_subgroup U u hu hcentral] at h
  exact h

theorem centralizer_translate_eq_generated_centralizer (U : Subgroup G) (u : G) :
    Subgroup.centralizer ((fun x : G => u * x) '' (U : Set G)) =
      Subgroup.centralizer ((Subgroup.closure ({u} : Set G) ⊔ U : Subgroup G) : Set G) := by
  rw [← Subgroup.centralizer_closure, closure_translate_eq_sup]

@[expose] def cosetClosureConjugation (Delta : Set G) :
    Subgroup.normalizer Delta →* MulAut (Subgroup.closure Delta) :=
  (Subgroup.closure Delta).normalizerMonoidHom.comp
    (Subgroup.inclusion (Subgroup.normalizer_le_normalizer_closure Delta))

theorem cosetClosureConjugation_ker_eq_entire_centralizer (Delta : Set G) :
    (cosetClosureConjugation Delta).ker =
      (Subgroup.centralizer Delta).subgroupOf (Subgroup.normalizer Delta) := by
  ext x
  change (Subgroup.closure Delta).normalizerMonoidHom
      (Subgroup.inclusion (Subgroup.normalizer_le_normalizer_closure Delta) x) = 1 ↔
    (x : G) ∈ Subgroup.centralizer Delta
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
  change (x : G) ∈ Subgroup.centralizer (Subgroup.closure Delta : Set G) ↔
    (x : G) ∈ Subgroup.centralizer Delta
  rw [Subgroup.centralizer_closure]

theorem cosetClosureConjugation_ker_map_eq_entire_centralizer (Delta : Set G) :
    (cosetClosureConjugation Delta).ker.map (Subgroup.normalizer Delta).subtype =
      Subgroup.centralizer Delta := by
  rw [cosetClosureConjugation_ker_eq_entire_centralizer]
  exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.centralizer_le_normalizer Delta)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
