module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {p f : ℕ} {E : Type} [Field E] {h : UnitaryFieldData p f E}
  {V : Type} [AddCommGroup V] [Module E V] {τ : V →ₛₗ[h.bar] V} (hττ : ∀ v, τ (τ v) = v)
  {c : E} (hc : h.bar c ≠ c)

include hc in
theorem mem_fixedField_decomp (a : E) :
    (c - h.bar c)⁻¹ * (a - h.bar a) ∈ h.fixedField ∧
      a - c * ((c - h.bar c)⁻¹ * (a - h.bar a)) ∈ h.fixedField := by
  have hc0 : c - h.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hbc0 : h.bar c - c ≠ 0 := sub_ne_zero.mpr hc
  constructor
  · rw [h.mem_fixedField, map_mul, map_inv₀, map_sub, map_sub, h.bar_bar, h.bar_bar, ← neg_sub c,
      ← neg_sub a, inv_neg, neg_mul_neg]
  · rw [h.mem_fixedField, map_sub, map_mul, map_mul, map_inv₀, map_sub, map_sub, h.bar_bar,
      h.bar_bar]
    field_simp
    ring

include hττ in
theorem inv_smul_sub_mem_conjFixed (v : V) : (c - h.bar c)⁻¹ • (v - τ v) ∈ conjFixed h τ := by
  rw [mem_conjFixed, map_smulₛₗ, map_sub, hττ, map_inv₀, map_sub, h.bar_bar, ← neg_sub c,
    inv_neg, neg_smul, ← smul_neg, neg_sub]

include hττ hc in
theorem sub_smul_inv_smul_mem_conjFixed (v : V) :
    v - c • ((c - h.bar c)⁻¹ • (v - τ v)) ∈ conjFixed h τ := by
  have hw := inv_smul_sub_mem_conjFixed hττ (c := c) v
  rw [mem_conjFixed] at hw ⊢
  rw [map_sub, map_smulₛₗ, hw]
  have hc0 : c - h.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have key : (c - h.bar c) • ((c - h.bar c)⁻¹ • (v - τ v)) = v - τ v := by
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [sub_smul, sub_eq_iff_eq_add] at key
  rw [sub_eq_sub_iff_add_eq_add, key]
  abel

include hττ hc in
theorem span_conjFixed_of_ne : Submodule.span E (conjFixed h τ : Set V) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : v = (v - c • ((c - h.bar c)⁻¹ • (v - τ v))) + c • ((c - h.bar c)⁻¹ • (v - τ v)) :=
    (sub_add_cancel _ _).symm
  rw [hv]
  exact add_mem (Submodule.subset_span (sub_smul_inv_smul_mem_conjFixed hττ hc v))
    (Submodule.smul_mem _ _ (Submodule.subset_span (inv_smul_sub_mem_conjFixed hττ v)))

include hc in
theorem eq_zero_of_add_smul_eq_zero {w₀ w₁ : V} (h₀ : w₀ ∈ conjFixed h τ)
    (h₁ : w₁ ∈ conjFixed h τ) (hw : w₀ + c • w₁ = 0) : w₀ = 0 ∧ w₁ = 0 := by
  have h2 : w₀ + h.bar c • w₁ = 0 := by
    have h3 := congrArg τ hw
    rwa [map_add, map_smulₛₗ, map_zero, mem_conjFixed.mp h₀, mem_conjFixed.mp h₁] at h3
  have h3 : (c - h.bar c) • w₁ = 0 := by
    rw [sub_smul, show c • w₁ - h.bar c • w₁ = (w₀ + c • w₁) - (w₀ + h.bar c • w₁) by abel, hw,
      h2, sub_zero]
  have hw₁ : w₁ = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  refine ⟨?_, hw₁⟩
  rw [hw₁, smul_zero, add_zero] at hw
  exact hw

include hc in
theorem linearIndependent_conjFixed_of_ne {ι : Type*} (b : Basis ι h.fixedField (conjFixed h τ)) :
    LinearIndependent E (fun i => (b i : V)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  obtain ⟨y, hy⟩ : ∃ y : ι → h.fixedField,
      ∀ j, (y j : E) = (c - h.bar c)⁻¹ * (g j - h.bar (g j)) :=
    ⟨fun j => ⟨_, (mem_fixedField_decomp hc (g j)).1⟩, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ι → h.fixedField, ∀ j, (x j : E) = g j - c * (y j : E) :=
    ⟨fun j => ⟨_, (mem_fixedField_decomp hc (g j)).2⟩, fun j => by rw [hy]⟩
  have hgj : ∀ j, g j = (x j : E) + c * (y j : E) := fun j => by
    rw [hx]
    ring
  have hg' : ((∑ j ∈ s, x j • b j : conjFixed h τ) : V) +
      c • ((∑ j ∈ s, y j • b j : conjFixed h τ) : V) = 0 := by
    rw [← hg, Submodule.coe_sum, Submodule.coe_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Submodule.coe_smul, Subfield.smul_def, Subfield.smul_def, smul_smul,
      ← add_smul, ← hgj]
  obtain ⟨h1, h3⟩ := eq_zero_of_add_smul_eq_zero hc (Submodule.coe_mem _) (Submodule.coe_mem _) hg'
  have hx0 := (linearIndependent_iff'.mp b.linearIndependent) s x
    (by rw [← Submodule.coe_eq_zero]; exact h1) i hi
  have hy0 := (linearIndependent_iff'.mp b.linearIndependent) s y
    (by rw [← Submodule.coe_eq_zero]; exact h3) i hi
  rw [hgj i, hx0, hy0, ZeroMemClass.coe_zero, mul_zero, add_zero]

include hττ hc in
theorem span_basis_conjFixed_of_ne {ι : Type*} (b : Basis ι h.fixedField (conjFixed h τ)) :
    ⊤ ≤ Submodule.span E (Set.range fun i => (b i : V)) := by
  rw [← span_conjFixed_of_ne hττ hc, Submodule.span_le]
  intro w hw
  exact Submodule.span_induction (p := fun x _ => ((x : conjFixed h τ) : V) ∈
      Submodule.span E (Set.range fun i => (b i : V)))
    (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      exact Submodule.subset_span ⟨j, rfl⟩)
    (Submodule.zero_mem _)
    (fun x y _ _ hx hy => by
      rw [Submodule.coe_add]
      exact add_mem hx hy)
    (fun a x _ hx => by
      rw [Submodule.coe_smul, Subfield.smul_def]
      exact Submodule.smul_mem _ _ hx)
    (b.mem_span ⟨w, hw⟩)

@[expose] noncomputable def conjFixedBasisOfNe {ι : Type*}
    (b : Basis ι h.fixedField (conjFixed h τ)) : Basis ι E V :=
  Basis.mk (linearIndependent_conjFixed_of_ne hc b) (span_basis_conjFixed_of_ne hττ hc b)

theorem conjFixedBasisOfNe_apply {ι : Type*} (b : Basis ι h.fixedField (conjFixed h τ))
    (i : ι) : conjFixedBasisOfNe hττ hc b i = b i :=
  Basis.mk_apply _ _ i

include hττ hc in
theorem finrank_conjFixed_of_ne [FiniteDimensional E V] :
    finrank h.fixedField (conjFixed h τ) = finrank E V := by
  have := finite_conjFixed (h := h) (τ := τ)
  rw [finrank_eq_card_basis (conjFixedBasisOfNe hττ hc
    (Module.finBasis h.fixedField (conjFixed h τ))), Fintype.card_fin]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
