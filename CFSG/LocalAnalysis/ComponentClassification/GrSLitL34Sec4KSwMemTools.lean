module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_coreActionKernel_of_conj_mem_oddIn {X F : Subgroup G} {c : G} (hFX : F ≤ X)
    (hsup : F ⊔ oddIn X = X) (hcN : c ∈ normalizer (X : Set G))
    (hc : ∀ y ∈ F, c * y * c⁻¹ * y⁻¹ ∈ oddIn X) : c ∈ coreActionKernel X := by
  have hON : ∀ {g : G}, g ∈ normalizer (X : Set G) → ∀ o ∈ oddIn X, g * o * g⁻¹ ∈ oddIn X :=
    fun hg o ho => GrS4.conj_mem_oddIn_of_mem_normalizer hg ho
  have hset : ((X : Subgroup G) : Set G) = (F : Set G) * (oddIn X : Set G) := by
    conv_lhs => rw [← hsup]
    exact coe_mul_of_left_le_normalizer_right _ _ (hFX.trans (GrS4.self_le_normalizer_oddIn X))
  have hcj : ∀ j ∈ X, c * j * c⁻¹ * j⁻¹ ∈ oddIn X := by
    intro j hj
    have hj' : j ∈ (F : Set G) * (oddIn X : Set G) := hset ▸ hj
    obtain ⟨y, hy, o, ho, rfl⟩ := hj'
    have hco : c * o * c⁻¹ ∈ oddIn X := hON hcN o ho
    have e : c * (y * o) * c⁻¹ * (y * o)⁻¹ =
        (c * y * c⁻¹ * y⁻¹) * (y * ((c * o * c⁻¹) * o⁻¹) * y⁻¹) := by group
    rw [e]
    exact mul_mem (hc y hy) (hON (le_normalizer (hFX hy)) _ (mul_mem hco (inv_mem ho)))
  refine mem_coreActionKernel.mpr ⟨hcN, fun j hj => ?_⟩
  have h1 := hON (inv_mem hcN) _ (hcj j⁻¹ (inv_mem hj))
  rwa [show c⁻¹ * (c * j⁻¹ * c⁻¹ * j⁻¹⁻¹) * c⁻¹⁻¹ = j⁻¹ * c⁻¹ * j * c by group] at h1

theorem mem_withKernel_of_fixedLayer {X Y F : Subgroup G} (hFX : F ≤ X) (hFY : F ≤ Y)
    (hXsup : F ⊔ oddIn X = X) (hYsup : F ⊔ oddIn Y = Y) {s : G} (hsX : s ∈ withKernel X)
    (hsY : s ∈ normalizer (Y : Set G)) (hsF : s ∈ normalizer (F : Set G)) :
    s ∈ withKernel Y := by
  have hXC : X ≤ normalizer (coreActionKernel X : Set G) := fun y hy =>
    UnbalancedLayer.normalizer_le_normalizer_coreActionKernel X (le_normalizer hy)
  have hs' : s ∈ (X : Set G) * (coreActionKernel X : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hXC]
    exact hsX
  obtain ⟨j, hj, c, hc, rfl⟩ := hs'
  have hset : ((X : Subgroup G) : Set G) = (F : Set G) * (oddIn X : Set G) := by
    conv_lhs => rw [← hXsup]
    exact coe_mul_of_left_le_normalizer_right _ _ (hFX.trans (GrS4.self_le_normalizer_oddIn X))
  have hj' : j ∈ (F : Set G) * (oddIn X : Set G) := hset ▸ hj
  obtain ⟨f, hf, o, ho, rfl⟩ := hj'
  have hc'X : o * c ∈ coreActionKernel X :=
    mul_mem (GrS4.oddIn_le_coreActionKernel X ho) hc
  have hc'eq : o * c = f⁻¹ * (f * o * c) := by group
  have hc'Y : o * c ∈ normalizer (Y : Set G) := by
    rw [hc'eq]
    exact mul_mem (inv_mem (le_normalizer (hFY hf))) hsY
  have hc'F : o * c ∈ normalizer (F : Set G) := by
    rw [hc'eq]
    exact mul_mem (inv_mem (le_normalizer hf)) hsF
  have hc'N : o * c ∈ normalizer (X : Set G) := (mem_coreActionKernel.mp hc'X).1
  have hOF : oddIn X ⊓ F ≤ oddIn Y :=
    (GrS5.inf_oddIn_le_oddIn hFX).trans (GrS4.oddIn_le_oddIn_of_eq_sup hFY hYsup.symm)
  have hc'K : o * c ∈ coreActionKernel Y := by
    refine mem_coreActionKernel_of_conj_mem_oddIn hFY hYsup hc'Y fun y hy => hOF ?_
    refine mem_inf.mpr ⟨?_, mul_mem ((mem_normalizer_iff.mp hc'F y).mp hy) (inv_mem hy)⟩
    have h1 := (mem_coreActionKernel.mp hc'X).2 y⁻¹ (inv_mem (hFX hy))
    have h2 := GrS4.conj_mem_oddIn_of_mem_normalizer hc'N h1
    rwa [show o * c * (y⁻¹⁻¹ * (o * c)⁻¹ * y⁻¹ * (o * c)) * (o * c)⁻¹ =
      o * c * y * (o * c)⁻¹ * y⁻¹ by group] at h2
  show f * o * c ∈ withKernel Y
  rw [show f * o * c = f * (o * c) by group]
  exact mul_mem (mem_sup_left (hFY hf)) (mem_sup_right hc'K)

end CFSG.ComponentClassification.GrSLit.KSw
