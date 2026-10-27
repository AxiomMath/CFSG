module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Basic

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup

@[expose] def OutSq (A : Type*) [Group A] : Prop :=
  ∀ α : A ≃* A, ∃ a : A, ∀ x, α (α x) = a * x * a⁻¹

@[expose] def OutAbel (A : Type*) [Group A] : Prop :=
  ∀ α β : A ≃* A, ∃ c : A, ∀ x, α (β x) = c * β (α x) * c⁻¹

variable {A : Type*} [Group A]

instance innerNormal : ((MulAut.conj : A →* MulAut A).range).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ g
    refine ⟨g a, ?_⟩
    ext x
    simp [MulAut.conj_apply]

theorem OutSq.abel (h : OutSq A) : OutAbel A := by
  intro α β
  let N : Subgroup (MulAut A) := (MulAut.conj : A →* MulAut A).range
  have hsq : ∀ γ : MulAut A, γ * γ ∈ N := by
    intro γ
    obtain ⟨a, ha⟩ := h γ
    refine ⟨a, ?_⟩
    ext x
    simp [MulAut.conj_apply, ha x, MulAut.mul_apply]
  have hcomm : α * β * α⁻¹ * β⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk' N α) * QuotientGroup.mk' N α = 1 := by
      rw [← map_mul]; exact (QuotientGroup.eq_one_iff _).2 (hsq α)
    have h2 : (QuotientGroup.mk' N β) * QuotientGroup.mk' N β = 1 := by
      rw [← map_mul]; exact (QuotientGroup.eq_one_iff _).2 (hsq β)
    have h3 : (QuotientGroup.mk' N α * QuotientGroup.mk' N β) *
        (QuotientGroup.mk' N α * QuotientGroup.mk' N β) = 1 := by
      rw [← map_mul, ← map_mul]; exact (QuotientGroup.eq_one_iff _).2 (hsq (α * β))
    have e1 : (QuotientGroup.mk' N α)⁻¹ = QuotientGroup.mk' N α := inv_eq_of_mul_eq_one_right h1
    have e2 : (QuotientGroup.mk' N β)⁻¹ = QuotientGroup.mk' N β := inv_eq_of_mul_eq_one_right h2
    show QuotientGroup.mk' N (α * β * α⁻¹ * β⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, e1, e2]
    simpa [mul_assoc] using h3
  obtain ⟨c, hc⟩ := hcomm
  refine ⟨c, fun x => ?_⟩
  have h1 := congrArg (fun φ : MulAut A => φ (β (α x))) hc
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply] at h1
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
  exact h1.symm

theorem OutSq.of_mulEquiv {B : Type*} [Group B] (e : A ≃* B) (h : OutSq A) : OutSq B := by
  intro β
  obtain ⟨a, ha⟩ := h (e.trans (β.trans e.symm))
  refine ⟨e a, fun y => ?_⟩
  have h1 := ha (e.symm y)
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
  have h2 := congrArg e h1
  simpa using h2

variable {K : Type*} [Group K]

def conjOn (S : Subgroup K) {y : K} (hy : y ∈ normalizer (S : Set K)) : ↥S ≃* ↥S where
  toFun s := ⟨y * s * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy _).1 s.2⟩
  invFun s := ⟨y⁻¹ * s * y, by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 s.2
    simpa using this⟩
  left_inv s := by
    apply Subtype.ext
    show y⁻¹ * (y * (s : K) * y⁻¹) * y = s
    group
  right_inv s := by
    apply Subtype.ext
    show y * (y⁻¹ * (s : K) * y) * y⁻¹ = s
    group
  map_mul' s t := by
    apply Subtype.ext
    show y * ((s : K) * t) * y⁻¹ = (y * s * y⁻¹) * (y * t * y⁻¹)
    group

theorem outCond_one {S : Subgroup K} (h : OutAbel ↥S) {y₁ y₂ : K}
    (hy₁ : y₁ ∈ normalizer (S : Set K)) (hy₂ : y₂ ∈ normalizer (S : Set K)) :
    ∃ c ∈ S, ∀ s ∈ S, (y₁ * y₂) * s * (y₁ * y₂)⁻¹ =
      c * ((y₂ * y₁) * s * (y₂ * y₁)⁻¹) * c⁻¹ := by
  obtain ⟨c, hc⟩ := h (conjOn S hy₁) (conjOn S hy₂)
  refine ⟨c, c.2, fun s hs => ?_⟩
  have h1 : y₁ * (y₂ * s * y₂⁻¹) * y₁⁻¹ = c * (y₂ * (y₁ * s * y₁⁻¹) * y₂⁻¹) * c⁻¹ :=
    congrArg Subtype.val (hc ⟨s, hs⟩)
  calc (y₁ * y₂) * s * (y₁ * y₂)⁻¹ = y₁ * (y₂ * s * y₂⁻¹) * y₁⁻¹ := by group
    _ = c * (y₂ * (y₁ * s * y₁⁻¹) * y₂⁻¹) * c⁻¹ := h1
    _ = c * ((y₂ * y₁) * s * (y₂ * y₁)⁻¹) * c⁻¹ := by group

theorem outCond_two {S : Subgroup K} (h : OutSq ↥S) {y : K}
    (hy : y ∈ normalizer (S : Set K)) :
    ∃ a ∈ S, ∀ s ∈ S, (y * y) * s * (y * y)⁻¹ = a * s * a⁻¹ := by
  obtain ⟨a, ha⟩ := h (conjOn S hy)
  refine ⟨a, a.2, fun s hs => ?_⟩
  have h1 : y * (y * s * y⁻¹) * y⁻¹ = a * s * a⁻¹ := congrArg Subtype.val (ha ⟨s, hs⟩)
  calc (y * y) * s * (y * y)⁻¹ = y * (y * s * y⁻¹) * y⁻¹ := by group
    _ = a * s * a⁻¹ := h1

end CFSG.EvenSporadicStandard.SolomonRed
