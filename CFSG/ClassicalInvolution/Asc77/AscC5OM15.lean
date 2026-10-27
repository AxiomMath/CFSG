module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM14

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {F : Type} [Field F] {M : gsp 2 F}

theorem gm_gm_mulVec_of_plus (hN : gm M * gm M = mu M • 1) (x : Fin 2 ⊕ Fin 2 → F) :
    gm M *ᵥ (gm M *ᵥ x) = mu M • x := by
  rw [Matrix.mulVec_mulVec, hN, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem form_gm_left_of_plus (hN : gm M * gm M = mu M • 1) (x y : Fin 2 ⊕ Fin 2 → F) :
    form (gm M *ᵥ x) y = form x (gm M *ᵥ y) := by
  have hμ : mu M ≠ 0 := Units.ne_zero _
  have h := form_gm_gm M (gm M *ᵥ x) y
  rw [gm_gm_mulVec_of_plus hN, form_smul_left] at h
  have h' : mu M * (form (gm M *ᵥ x) y - form x (gm M *ᵥ y)) = 0 := by linear_combination -h
  have := (mul_eq_zero.mp h').resolve_left hμ
  linear_combination this

theorem form_gm_self_of_plus (h2 : (2 : F) ≠ 0) (hN : gm M * gm M = mu M • 1)
    (x : Fin 2 ⊕ Fin 2 → F) : form x (gm M *ᵥ x) = 0 := by
  have h1 := form_gm_left_of_plus hN x x
  rw [form_antisymm] at h1
  have : (2 : F) * form x (gm M *ᵥ x) = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 this).resolve_left h2

@[expose] def nPlus (μ : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![0, μ; 1, 0] 0 0 !![0, 1; μ, 0]

theorem exists_conj_nPlus (h2 : (2 : F) ≠ 0) (hN : gm M * gm M = mu M • 1)
    (hns : ¬ IsSquare (mu M)) :
    ∃ g : StatedSp 2 F, mat 2 F g * nPlus (mu M) = gm M * mat 2 F g := by
  set μ := mu M with hμdef
  have hμ : μ ≠ 0 := Units.ne_zero _
  set e₀ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1 with he₀
  set f₀ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inr 0) 1 with hf₀
  have hef : form e₀ f₀ = 1 := by rw [he₀, hf₀, form_single_right]; simp
  set a := form (gm M *ᵥ e₀) f₀ with ha
  have hc0 : 1 - a * a / μ ≠ 0 := by
    intro h
    apply hns
    exact ⟨a, by field_simp at h; linear_combination h⟩
  set c := (1 - a * a / μ)⁻¹ with hc
  set w := c • (f₀ - (a / μ) • (gm M *ᵥ f₀)) with hw
  have hw1 : form e₀ w = 1 := by
    rw [hw, form_smul_right, form_sub_right', form_smul_right, hef, ← form_gm_left_of_plus hN,
      ← ha, hc, show 1 - a / μ * a = 1 - a * a / μ by ring]
    exact inv_mul_cancel₀ hc0
  have hw2 : form (gm M *ᵥ e₀) w = 0 := by
    rw [hw, form_smul_right, form_sub_right', form_smul_right, ← ha, form_gm_gm, hef]
    field_simp
    ring
  have q1 : form e₀ (gm M *ᵥ e₀) = 0 := form_gm_self_of_plus h2 hN e₀
  have q2 : form (gm M *ᵥ e₀) (μ⁻¹ • (gm M *ᵥ w)) = 1 := by
    rw [form_smul_right, form_gm_gm, hw1, mul_one, inv_mul_cancel₀ hμ]
  have q3 : form e₀ (μ⁻¹ • (gm M *ᵥ w)) = 0 := by
    rw [form_smul_right, ← form_gm_left_of_plus hN, hw2, mul_zero]
  have q4 : form w (gm M *ᵥ e₀) = 0 := by
    rw [form_antisymm, hw2, neg_zero]
  have q5 : form w (μ⁻¹ • (gm M *ᵥ w)) = 0 := by
    rw [form_smul_right, form_gm_self_of_plus h2 hN w, mul_zero]
  obtain ⟨g, g1, g2, g3, g4⟩ := exists_sp_apply_eq_two (m := 0) e₀ w (gm M *ᵥ e₀)
    (μ⁻¹ • (gm M *ᵥ w)) hw1 q2 q1 q3 q4 q5
  have g1' : mat 2 F g *ᵥ Pi.single (Sum.inl 0) 1 = e₀ := g1
  have g2' : mat 2 F g *ᵥ Pi.single (Sum.inr 0) 1 = w := g2
  have g3' : mat 2 F g *ᵥ Pi.single (Sum.inl 1) 1 = gm M *ᵥ e₀ := g3
  have g4' : mat 2 F g *ᵥ Pi.single (Sum.inr 1) 1 = μ⁻¹ • (gm M *ᵥ w) := g4
  have c1 : nPlus μ *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 1) 1 := by
    ext r; rw [mulVec_single_one_apply]; rcases r with r | r <;> fin_cases r <;> simp [nPlus]
  have c2 : nPlus μ *ᵥ Pi.single (Sum.inl 1) 1 = μ • Pi.single (Sum.inl 0) 1 := by
    ext r; rw [mulVec_single_one_apply]; rcases r with r | r <;> fin_cases r <;> simp [nPlus]
  have c3 : nPlus μ *ᵥ Pi.single (Sum.inr 0) 1 = μ • Pi.single (Sum.inr 1) 1 := by
    ext r; rw [mulVec_single_one_apply]; rcases r with r | r <;> fin_cases r <;> simp [nPlus]
  have c4 : nPlus μ *ᵥ Pi.single (Sum.inr 1) 1 = Pi.single (Sum.inr 0) 1 := by
    ext r; rw [mulVec_single_one_apply]; rcases r with r | r <;> fin_cases r <;> simp [nPlus]
  refine ⟨g, matrix_ext_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases j with j | j <;> fin_cases j
  · show mat 2 F g *ᵥ (nPlus μ *ᵥ Pi.single (Sum.inl 0) 1) =
      gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inl 0) 1)
    rw [c1, g3', g1']
  · show mat 2 F g *ᵥ (nPlus μ *ᵥ Pi.single (Sum.inl 1) 1) =
      gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inl 1) 1)
    rw [c2, Matrix.mulVec_smul, g1', g3', gm_gm_mulVec_of_plus hN]
  · show mat 2 F g *ᵥ (nPlus μ *ᵥ Pi.single (Sum.inr 0) 1) =
      gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inr 0) 1)
    rw [c3, Matrix.mulVec_smul, g4', g2', smul_smul, mul_inv_cancel₀ hμ, one_smul]
  · show mat 2 F g *ᵥ (nPlus μ *ᵥ Pi.single (Sum.inr 1) 1) =
      gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inr 1) 1)
    rw [c4, g2', g4', Matrix.mulVec_smul, gm_gm_mulVec_of_plus hN, smul_smul,
      inv_mul_cancel₀ hμ, one_smul]

end CFSG.ClassicalInvolution.Asc77.C5O.M
