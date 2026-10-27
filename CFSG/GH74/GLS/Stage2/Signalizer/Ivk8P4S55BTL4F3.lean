module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4F2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4B2
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag BS4
open scoped commutatorElement

variable {F : Type} [Field F]

abbrev MB (F : Type) [Field F] : Type := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

abbrev EigAlt (A₁ A₂ : GL (Fin 4) F) : Prop :=
  (∃ v : Fin 4 → F, v ≠ 0 ∧ ∃ ν₁ ν₂ : F, (A₁ : Matrix (Fin 4) (Fin 4) F) *ᵥ v = ν₁ • v ∧
      (A₂ : Matrix (Fin 4) (Fin 4) F) *ᵥ v = ν₂ • v) ∨
    (∃ v : Fin 4 → F, v ≠ 0 ∧ ∃ ν₁ ν₂ : F, v ᵥ* (A₁ : Matrix (Fin 4) (Fin 4) F) = ν₁ • v ∧
      v ᵥ* (A₂ : Matrix (Fin 4) (Fin 4) F) = ν₂ • v)

theorem eig_or_comm_two {H : Subgroup (GL (Fin 4) F)} {G : GL (Fin 4) F}
    (hst : ∀ x ∈ H, StabF 2 (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (x : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)))
    {A₁ A₂ : GL (Fin 4) F}
    (hs₁ : StabF 2 (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A₁ : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)))
    (hs₂ : StabF 2 (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A₂ : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)))
    (hA₁H : ∀ x ∈ H, A₁ * x = x * A₁) (hA₂H : ∀ x ∈ H, A₂ * x = x * A₂) :
    (∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z) ∨ EigAlt A₁ A₂ := by
  let φ : GL (Fin 4) F →* GL (Fin 2 ⊕ Fin 2) F := bvGL.comp (MulAut.conj G⁻¹).toMonoidHom
  have hφ : ∀ x, ((φ x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      bv (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) *
        (G : Matrix (Fin 4) (Fin 4) F)) := by
    intro x
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      coe_bvGL, Units.val_mul]
  have hφinj : Function.Injective φ := bvGL_injective.comp (MulAut.conj G⁻¹).injective
  have h21 : ∀ x : GL (Fin 4) F, StabF 2 (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (x : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) →
      ((φ x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 :=
    fun x hx => by rw [hφ]; exact toBlocks₂₁_bv_of_stabF2 hx
  have hH' : ∀ y ∈ H.map φ,
      ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    exact h21 x (hst x hx)
  have hcom : ∀ A : GL (Fin 4) F, StabF 2 (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) →
      (∀ x ∈ H, A * x = x * A) → ∀ x ∈ H,
      ((φ A : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ *
        ((φ x : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ =
        ((φ x : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ *
          ((φ A : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ ∧
      ((φ A : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ *
        ((φ x : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ =
        ((φ x : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ *
          ((φ A : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ := by
    intro A hA hAH x hx
    have e := congrArg (fun z => ((φ z : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (hAH x hx)
    simp only [map_mul, Units.val_mul] at e
    refine ⟨?_, ?_⟩
    · have := congrArg toBlocks₁₁ e
      rwa [ul_mul (h21 x (hst x hx)), ul_mul (h21 A hA)] at this
    · have := congrArg toBlocks₂₂ e
      rwa [lr_mul (h21 A hA), lr_mul (h21 x (hst x hx))] at this
  by_cases hul : ∀ y ∈ H.map φ, ∀ y' ∈ H.map φ,
      ((y : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ *
        ((y' : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ =
      ((y' : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ *
        ((y : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁
  · by_cases hlr : ∀ y ∈ H.map φ, ∀ y' ∈ H.map φ,
        ((y : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ *
          ((y' : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ =
        ((y' : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ *
          ((y : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂
    · left
      have hc := comm_of_blocks_comm hH' hul hlr
      have hmc : ⁅H.map φ, H.map φ⁆ = ⁅H, H⁆.map φ := (Subgroup.map_commutator H H φ).symm
      intro z hz w hw
      apply hφinj
      rw [map_mul, map_mul]
      exact hc _ (hmc ▸ ⟨z, hz, rfl⟩) _ (hmc ▸ ⟨w, hw, rfl⟩)
    · right
      right
      push Not at hlr
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hlr
      have hsc : ∀ A : GL (Fin 4) F, StabF 2 (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (A : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) →
          (∀ x ∈ H, A * x = x * A) →
          ∃ ν : F, ((φ A : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₂₂ = ν • 1 := by
        intro A hA hAH
        by_contra hns
        push Not at hns
        exact hxy (comm_of_comm_nonscalar hns (hcom A hA hAH x hx).2.symm
          (hcom A hA hAH y hy).2.symm)
      obtain ⟨ν₁, hν₁⟩ := hsc A₁ hs₁ hA₁H
      obtain ⟨ν₂, hν₂⟩ := hsc A₂ hs₂ hA₂H
      rw [hφ] at hν₁ hν₂
      exact ⟨_, vecMul_ne_zero ee3_ne_zero, ν₁, ν₂,
        roweig_of_conj (vecMul_e3_of_bv (toBlocks₂₁_bv_of_stabF2 hs₁) hν₁),
        roweig_of_conj (vecMul_e3_of_bv (toBlocks₂₁_bv_of_stabF2 hs₂) hν₂)⟩
  · right
    left
    push Not at hul
    obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hul
    have hsc : ∀ A : GL (Fin 4) F, StabF 2 (((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (A : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) →
        (∀ x ∈ H, A * x = x * A) →
        ∃ ν : F, ((φ A : GL (Fin 2 ⊕ Fin 2) F) : MB F).toBlocks₁₁ = ν • 1 := by
      intro A hA hAH
      by_contra hns
      push Not at hns
      exact hxy (comm_of_comm_nonscalar hns (hcom A hA hAH x hx).1.symm
        (hcom A hA hAH y hy).1.symm)
    obtain ⟨ν₁, hν₁⟩ := hsc A₁ hs₁ hA₁H
    obtain ⟨ν₂, hν₂⟩ := hsc A₂ hs₂ hA₂H
    rw [hφ] at hν₁ hν₂
    exact ⟨_, mulVec_ne_zero ee0_ne_zero, ν₁, ν₂,
      eig_of_conj (mulVec_e0_of_bv (toBlocks₂₁_bv_of_stabF2 hs₁) hν₁),
      eig_of_conj (mulVec_e0_of_bv (toBlocks₂₁_bv_of_stabF2 hs₂) hν₂)⟩

theorem eig_or_comm {H : Subgroup (GL (Fin 4) F)} {N : Submodule F (Fin 4 → F)}
    (hN0 : N ≠ ⊥) (hNt : N ≠ ⊤)
    (hHN : ∀ x ∈ H, ∀ v ∈ N, (x : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N)
    {A₁ A₂ : GL (Fin 4) F} (hA₁N : ∀ v ∈ N, (A₁ : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N)
    (hA₂N : ∀ v ∈ N, (A₂ : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N)
    (hA₁H : ∀ x ∈ H, A₁ * x = x * A₁) (hA₂H : ∀ x ∈ H, A₂ * x = x * A₂) :
    (∀ z ∈ ⁅H, H⁆, ∀ w ∈ ⁅H, H⁆, z * w = w * z) ∨ EigAlt A₁ A₂ := by
  obtain ⟨g, hg⟩ := exists_map_flagSpace_eq N
  have hst : ∀ M : Matrix (Fin 4) (Fin 4) F, (∀ v ∈ N, M *ᵥ v ∈ N) →
      StabF (finrank F N) ((((SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) * M * (g : Matrix (Fin 4) (Fin 4) F)) :=
    fun M hM => stabF_conj hg hM
  have hd0 : finrank F N ≠ 0 := fun h => hN0 (Submodule.finrank_eq_zero.mp h)
  have hd4 : finrank F N ≠ 4 := fun h => hNt (Submodule.eq_top_of_finrank_eq (by
    rw [h, finrank_fin_fun]))
  have hdle : finrank F N ≤ 4 := by simpa using Submodule.finrank_le N
  rcases (show finrank F N = 1 ∨ finrank F N = 2 ∨ finrank F N = 3 by omega) with h1 | h2 | h3
  · rw [h1] at hst
    exact Or.inr (Or.inl ⟨_, mulVec_ne_zero (G := SpecialLinearGroup.toGL g) ee0_ne_zero, _, _,
      eig_of_conj (mulVec_e0_of_stabF1 (hst _ hA₁N)),
      eig_of_conj (mulVec_e0_of_stabF1 (hst _ hA₂N))⟩)
  · rw [h2] at hst
    exact eig_or_comm_two (G := SpecialLinearGroup.toGL g) (fun x hx => hst _ (hHN x hx))
      (hst _ hA₁N) (hst _ hA₂N) hA₁H hA₂H
  · rw [h3] at hst
    exact Or.inr (Or.inr ⟨_, vecMul_ne_zero ee3_ne_zero, _, _,
      roweig_of_conj (vecMul_e3_of_stabF3 (hst _ hA₁N)),
      roweig_of_conj (vecMul_e3_of_stabF3 (hst _ hA₂N))⟩)

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
