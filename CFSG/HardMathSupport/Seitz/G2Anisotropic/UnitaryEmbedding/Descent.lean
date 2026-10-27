module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoLang
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SylowPairs
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.QPlusModel
public import CFSG.Quasithin.Background.G2URoots

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.ComponentClassification.UnbalancedCatalog

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

omit [Finite K₂] in
theorem exists_map_eq_of_fixed (hdeg : Module.finrank K K₂ = 2) (hσ : ∀ c, σ c = c ^ Nat.card K)
    (D : SL2 K₂) (hD : Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) D = D) :
    ∃ A : SL2 K, Matrix.SpecialLinearGroup.map (algebraMap K K₂) A = D := by
  obtain ⟨-, -, hfix⟩ := quadratic_frobenius hdeg σ hσ
  choose f hf using fun i j => (hfix (D i j)).1 (by
    have := congrArg (fun X : SL2 K₂ => (X : Matrix (Fin 2) (Fin 2) K₂) i j) hD
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this)
  have hmap : (algebraMap K K₂).mapMatrix (Matrix.of f) = (D : Matrix (Fin 2) (Fin 2) K₂) := by
    ext i j
    simp [hf]
  have hdet : (Matrix.of f).det = 1 := by
    apply (algebraMap K K₂).injective
    rw [RingHom.map_det, hmap, map_one]
    exact D.2
  let A : SL2 K := ⟨Matrix.of f, hdet⟩
  refine ⟨A, Subtype.ext ?_⟩
  exact hmap

theorem exists_rootSL2_of_baseChange (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {β : Fin Tag.G2.rank → ℤ} {y : ModGL .G2 K}
    {D : SL2 K₂} (h : baseChangeGL (algebraMap K K₂) y = rootSL2 .G2 K₂ β D) :
    ∃ A : SL2 K, y = rootSL2 .G2 K β A := by
  have hfixy := entrywise_baseChangeGL_fixed hσ y
  rw [h, entrywise_rootSL2_of_field] at hfixy
  have hD := rootSL2_injective_of_field β hfixy
  obtain ⟨A, hA⟩ := exists_map_eq_of_fixed hdeg hσ D hD
  refine ⟨A, baseChangeGL_injective (τ := .G2) (algebraMap K K₂) ?_⟩
  rw [h, baseChangeGL_rootSL2_of_field, hA]

theorem rootSL2_a_conj_v (L : Type) [Field L] (Y C : SL2 L) :
    rootSL2 .G2 L g2a Y * rootSL2 .G2 L g2v C * (rootSL2 .G2 L g2a Y)⁻¹ =
      rootSL2 .G2 L g2v C := by
  rw [← rootSL2_g2v_mul_rootSL2_g2a C Y, mul_assoc, mul_inv_cancel, mul_one]

theorem rootSL2_v_conj_a (L : Type) [Field L] (Y C : SL2 L) :
    rootSL2 .G2 L g2v Y * rootSL2 .G2 L g2a C * (rootSL2 .G2 L g2v Y)⁻¹ =
      rootSL2 .G2 L g2a C := by
  rw [rootSL2_g2v_mul_rootSL2_g2a Y C, mul_assoc, mul_inv_cancel, mul_one]

theorem QPlusModel.g_conj_v (M : QPlusModel K σ) (X : SL2 K₂) :
    M.g * rootSL2 .G2 K₂ g2v X * M.g⁻¹ = rootSL2 .G2 K₂ g2v (M.P⁻¹ * X * M.P) := by
  rw [M.hgdef]
  have h2 : rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2v X *
      (rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹ =
      rootSL2 .G2 K₂ g2a M.P⁻¹ * (rootSL2 .G2 K₂ g2v (M.P⁻¹ * X * M.P)) *
        (rootSL2 .G2 K₂ g2a M.P⁻¹)⁻¹ := by
    simp only [map_mul, map_inv, mul_inv_rev, mul_assoc, inv_inv]
  rw [h2, rootSL2_a_conj_v]

theorem QPlusModel.g_conj_a (M : QPlusModel K σ) (X : SL2 K₂) :
    M.g * rootSL2 .G2 K₂ g2a X * M.g⁻¹ = rootSL2 .G2 K₂ g2a (M.P⁻¹ * X * M.P) := by
  rw [M.hgdef]
  have h1 : rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2a X * (rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹ =
      rootSL2 .G2 K₂ g2a X := rootSL2_v_conj_a K₂ _ _
  have h2 : rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2a X *
      (rootSL2 .G2 K₂ g2a M.P⁻¹ * rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹ =
      rootSL2 .G2 K₂ g2a M.P⁻¹ * (rootSL2 .G2 K₂ g2v M.P⁻¹ * rootSL2 .G2 K₂ g2a X *
        (rootSL2 .G2 K₂ g2v M.P⁻¹)⁻¹) * (rootSL2 .G2 K₂ g2a M.P⁻¹)⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  rw [h2, h1]
  simp only [map_mul, map_inv, mul_assoc, inv_inv]

theorem QPlusModel.baseChange_eq_of_twist_v (M : QPlusModel K σ) {y : adjointGroup .G2 K}
    {C : SL2 K₂} (h : twistEmb (K := K) M.g y = rootSL2 .G2 K₂ g2v C) :
    baseChangeGL (algebraMap K K₂) (y : ModGL .G2 K) =
      rootSL2 .G2 K₂ g2v (M.P * C * M.P⁻¹) := by
  have h1 : M.g * baseChangeGL (algebraMap K K₂) (y : ModGL .G2 K) * M.g⁻¹ =
      M.g * rootSL2 .G2 K₂ g2v (M.P * C * M.P⁻¹) * M.g⁻¹ := by
    rw [M.g_conj_v, show M.P⁻¹ * (M.P * C * M.P⁻¹) * M.P = C by group]
    exact h
  exact mul_left_cancel (mul_right_cancel h1)

theorem QPlusModel.baseChange_eq_of_twist_a (M : QPlusModel K σ) {y : adjointGroup .G2 K}
    {C : SL2 K₂} (h : twistEmb (K := K) M.g y = rootSL2 .G2 K₂ g2a C) :
    baseChangeGL (algebraMap K K₂) (y : ModGL .G2 K) =
      rootSL2 .G2 K₂ g2a (M.P * C * M.P⁻¹) := by
  have h1 : M.g * baseChangeGL (algebraMap K K₂) (y : ModGL .G2 K) * M.g⁻¹ =
      M.g * rootSL2 .G2 K₂ g2a (M.P * C * M.P⁻¹) * M.g⁻¹ := by
    rw [M.g_conj_a, show M.P⁻¹ * (M.P * C * M.P⁻¹) * M.P = C by group]
    exact h
  exact mul_left_cancel (mul_right_cancel h1)

end CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding
