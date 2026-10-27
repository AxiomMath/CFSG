module

public import CFSG.ClassicalGroups.Alternating.I4SpLineElt

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

@[expose] noncomputable def quadPlus (BN : BilinForm K N) {π₀ π₀' : Submodule K N}
    (h : IsCompl π₀ π₀') (v : N) : K :=
  BN (π₀.projectionOnto π₀' h v : N) (π₀'.projectionOnto π₀ h.symm v : N)

variable {π₀ π₀' : Submodule K N} (h : IsCompl π₀ π₀')

theorem projectionOnto_add_of_mem {x y : N} (hx : x ∈ π₀) (hy : y ∈ π₀') :
    (π₀.projectionOnto π₀' h (x + y) : N) = x ∧
      (π₀'.projectionOnto π₀ h.symm (x + y) : N) = y := by
  constructor
  · rw [map_add, Submodule.projectionOnto_apply_of_mem_left h hx,
      Submodule.projectionOnto_apply_of_mem_right h hy, add_zero]
  · rw [map_add, Submodule.projectionOnto_apply_of_mem_right h.symm hx,
      Submodule.projectionOnto_apply_of_mem_left h.symm hy, zero_add]

include h in
theorem exists_add_eq_of_isCompl (v : N) : ∃ x ∈ π₀, ∃ y ∈ π₀', x + y = v := by
  have : v ∈ π₀ ⊔ π₀' := by rw [h.sup_eq_top]; trivial
  exact Submodule.mem_sup.mp this

theorem quadPlus_add_of_mem {x y : N} (hx : x ∈ π₀) (hy : y ∈ π₀') :
    quadPlus BN h (x + y) = BN x y := by
  rw [quadPlus, (projectionOnto_add_of_mem h hx hy).1, (projectionOnto_add_of_mem h hx hy).2]

theorem quadPlus_of_mem_right {y : N} (hy : y ∈ π₀') : quadPlus BN h y = 0 := by
  have := quadPlus_add_of_mem (BN := BN) h (zero_mem π₀) hy
  rwa [zero_add, map_zero, LinearMap.zero_apply] at this

theorem quadPlus_smul (c : K) (x : N) : quadPlus BN h (c • x) = c ^ 2 * quadPlus BN h x := by
  simp only [quadPlus, map_smul, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem quadPlus_add [CharP K 2] (hBN : BN.IsAlt) (hπ₀ : ∀ x ∈ π₀, ∀ y ∈ π₀, BN x y = 0)
    (hπ₀' : ∀ x ∈ π₀', ∀ y ∈ π₀', BN x y = 0) (x y : N) :
    quadPlus BN h (x + y) = quadPlus BN h x + quadPlus BN h y + BN x y := by
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := exists_add_eq_of_isCompl h x
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := exists_add_eq_of_isCompl h y
  have hs : (x₀ + x₁) + (y₀ + y₁) = (x₀ + y₀) + (x₁ + y₁) := by abel
  rw [hs, quadPlus_add_of_mem h (π₀.add_mem hx₀ hy₀) (π₀'.add_mem hx₁ hy₁),
    quadPlus_add_of_mem h hx₀ hx₁, quadPlus_add_of_mem h hy₀ hy₁]
  have hc : BN y₀ x₁ = BN x₁ y₀ := form_comm_charTwo hBN _ _
  simp only [map_add, LinearMap.add_apply, hπ₀ x₀ hx₀ y₀ hy₀, hπ₀' x₁ hx₁ y₁ hy₁, hc]
  ring

end CFSG.ClassicalGroups.Alternating
