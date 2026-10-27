module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

variable {L L' P : Type} [Group L] [Group L'] [Group P]

structure IsSubIso (N : Subgroup L) (N' : Subgroup L') (φ : L → L') : Prop where
  map_mul : ∀ x ∈ N, ∀ y ∈ N, φ (x * y) = φ x * φ y
  mem : ∀ x ∈ N, φ x ∈ N'
  inj : ∀ x ∈ N, ∀ y ∈ N, φ x = φ y → x = y
  surj : ∀ y ∈ N', ∃ x ∈ N, φ x = y

@[expose] def Compat (N : Subgroup L) (φ : L → L') (l : L) (l' : L') : Prop :=
  ∀ x ∈ N, φ (l * x * l⁻¹) = l' * φ x * l'⁻¹

@[expose] def fibre (θ : L →* P) (θ' : L' →* P) (ψ : P ≃* P) (N : Subgroup L) [N.Normal]
    (φ : L → L') : Subgroup (L × L') where
  carrier := {p | θ' p.2 = ψ (θ p.1) ∧ Compat N φ p.1 p.2}
  one_mem' := by
    refine ⟨by simp, fun x hx => ?_⟩
    simp
  mul_mem' := by
    rintro ⟨l₁, l₁'⟩ ⟨l₂, l₂'⟩ ⟨h₁, c₁⟩ ⟨h₂, c₂⟩
    refine ⟨by simp_all, fun x hx => ?_⟩
    have hx' : l₂ * x * l₂⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem x hx l₂
    have e1 : l₁ * l₂ * x * (l₁ * l₂)⁻¹ = l₁ * (l₂ * x * l₂⁻¹) * l₁⁻¹ := by group
    show φ (l₁ * l₂ * x * (l₁ * l₂)⁻¹) = l₁' * l₂' * φ x * (l₁' * l₂')⁻¹
    rw [e1, c₁ _ hx', c₂ x hx]
    group
  inv_mem' := by
    rintro ⟨l, l'⟩ ⟨h, c⟩
    refine ⟨by simp_all, fun x hx => ?_⟩
    have hy : l⁻¹ * x * l ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem x hx l⁻¹
    have e1 : l * (l⁻¹ * x * l) * l⁻¹ = x := by group
    have key := c _ hy
    rw [e1] at key
    show φ (l⁻¹ * x * l⁻¹⁻¹) = l'⁻¹ * φ x * l'⁻¹⁻¹
    rw [inv_inv, key]
    group

theorem mem_fibre_iff (θ : L →* P) (θ' : L' →* P) (ψ : P ≃* P) (N : Subgroup L) [N.Normal]
    (φ : L → L') (l : L) (l' : L') :
    (l, l') ∈ fibre θ θ' ψ N φ ↔ θ' l' = ψ (θ l) ∧ Compat N φ l l' := Iff.rfl

@[expose] def diag (N : Subgroup L) (φ : L → L') (hφ : ∀ x ∈ N, ∀ y ∈ N, φ (x * y) = φ x * φ y) :
    Subgroup (L × L') where
  carrier := {p | p.1 ∈ N ∧ p.2 = φ p.1}
  one_mem' := by
    refine ⟨N.one_mem, ?_⟩
    have h := hφ 1 N.one_mem 1 N.one_mem
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm).symm
  mul_mem' := by
    rintro ⟨x, x'⟩ ⟨y, y'⟩ ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨N.mul_mem hx hy, ?_⟩
    show x' * y' = φ (x * y)
    rw [hφ x hx y hy]
    simp_all
  inv_mem' := by
    rintro ⟨x, x'⟩ ⟨hx, hx'⟩
    refine ⟨N.inv_mem hx, ?_⟩
    show x'⁻¹ = φ x⁻¹
    have h := hφ x hx x⁻¹ (N.inv_mem hx)
    rw [mul_inv_cancel] at h
    have h1 : φ 1 = 1 := by
      have h' := hφ 1 N.one_mem 1 N.one_mem
      rw [mul_one] at h'
      exact mul_eq_left.mp h'.symm
    rw [h1] at h
    have hx'' : x' = φ x := hx'
    rw [hx'']
    exact (eq_inv_of_mul_eq_one_right h.symm).symm

end CFSG.EvenSporadicStandard.HNRecog.ML1
