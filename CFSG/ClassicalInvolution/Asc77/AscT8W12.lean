module

public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4Mat
public import CFSG.ClassicalInvolution.Models.Transfer.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherRigidity

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Chain

variable {F : Type} [Field F]

@[expose] def negTwo (F : Type) [Field F] : SL(4, F) :=
  ⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩

theorem coe_negTwo : ((negTwo F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := rfl

theorem blockMat_four_one (A : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 4 1 A =
      !![1, 0, 0, 0; 0, A 0 0, A 0 1, 0; 0, A 1 0, A 1 1, 0; 0, 0, 0, 1] := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem closure_union_eq_top (Mgl : GL (Fin 4) F) (S₁ S₂ : Set SL(4, F))
    (h₁ : ∀ i : Fin 3, i ≠ 2 → ∀ s ∈ (blockSL2 F 3 i).range,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s ∈ S₁)
    (h₂ : ∀ i : Fin 3, i ≠ 0 → ∀ s ∈ (blockSL2 F 3 i).range,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s ∈ S₂) :
    Subgroup.closure (S₁ ∪ S₂) = ⊤ := by
  set c := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl with hc
  have hgen : ⨆ i : Fin 3, ((blockSL2 F 3 i).range).map c.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_iSup, iSup_range_blockSL2 (K := F) 3, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr c.surjective]
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun i => ?_
  rintro _ ⟨s, hs, rfl⟩
  apply Subgroup.subset_closure
  by_cases hi2 : i = 2
  · exact Or.inr (h₂ i (by rw [hi2]; decide) s hs)
  · exact Or.inl (h₁ i hi2 s hs)

theorem closure_fix_eq_top {X : Type} [Group X] (ψ : SL(4, F) →* X)
    (hψ : Function.Surjective ψ) (σ : MulAut X) (α : SL(4, F) →* SL(4, F))
    (hlift : ∀ x, ψ (α x) = σ (ψ x)) (y : SL(4, F)) (Mgl : GL (Fin 4) F)
    (h₁ : ∀ i : Fin 3, i ≠ 2 → ∀ s ∈ (blockSL2 F 3 i).range,
      α (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s) =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s)
    (h₂ : ∀ i : Fin 3, i ≠ 0 → ∀ s ∈ (blockSL2 F 3 i).range,
      α (y * CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s *
        y⁻¹) =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s) :
    Subgroup.closure ({g | σ g = g} ∪ {g | σ (ψ y * g * (ψ y)⁻¹) = g}) = ⊤ := by
  set C := Subgroup.closure ({g | σ g = g} ∪ {g | σ (ψ y * g * (ψ y)⁻¹) = g}) with hC
  have hcl := closure_union_eq_top Mgl {x | α x = x} {x | α (y * x * y⁻¹) = x}
    (fun i hi s hs => h₁ i hi s hs) (fun i hi s hs => h₂ i hi s hs)
  have hle : Subgroup.closure ({x | α x = x} ∪ {x | α (y * x * y⁻¹) = x} : Set SL(4, F)) ≤
      C.comap ψ := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · apply Subgroup.subset_closure
      left
      show σ (ψ x) = ψ x
      rw [← hlift, show α x = x from hx]
    · apply Subgroup.subset_closure
      right
      show σ (ψ y * ψ x * (ψ y)⁻¹) = ψ x
      have : σ (ψ y * ψ x * (ψ y)⁻¹) = ψ (α (y * x * y⁻¹)) := by
        rw [hlift]
        congr 1
        rw [map_mul, map_mul, map_inv]
      rw [this, show α (y * x * y⁻¹) = x from hx]
  rw [hcl] at hle
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := hψ g
  exact hle (Subgroup.mem_top x)

end Chain

section Inner

variable {F : Type} [Field F]

theorem mapMatrix_refl' (X : Matrix (Fin 4) (Fin 4) F) : (RingEquiv.refl F).mapMatrix X = X := by
  ext i j
  simp

theorem alpha_fix_of_comm {G Gi : Matrix (Fin 4) (Fin 4) F} (hGGi : G * Gi = 1)
    {x : Matrix (Fin 4) (Fin 4) F} (h : G * x = x * G) : G * x * Gi = x := by
  rw [h, Matrix.mul_assoc, hGGi, Matrix.mul_one]

theorem sq_scalar_of_commute (M : Matrix (Fin 4) (Fin 4) F)
    (h : ∀ x : SL(4, F), M * (x : Matrix (Fin 4) (Fin 4) F) = (x : Matrix (Fin 4) (Fin 4) F) * M) :
    ∃ c : F, Matrix.scalar (Fin 4) c = M := by
  have := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := M) (fun t =>
    (h ⟨t.toMatrix, t.det⟩).symm)
  exact this

end Inner

end CFSG.ClassicalInvolution.Asc77.T8W
