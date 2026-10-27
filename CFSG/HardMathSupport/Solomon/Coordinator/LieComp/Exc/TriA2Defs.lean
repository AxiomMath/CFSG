module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Weyl
public import CFSG.LieType.Steinberg.TwistedD4.RankOne

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

noncomputable abbrev xa (a : ℕ) (u : K) : adjointGroup d4 K :=
  xPar (rootOperatorFamily d4) (d4Root a) u

section Defs

variable (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

noncomputable def slSh : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup d4 K :=
  (twistedGroup σ).subtype.comp (slShort σ hσ)

noncomputable def fP1 (c : K) : adjointGroup d4 K := slSh σ hσ (sl2Upper c)

noncomputable def fM1 (c : K) : adjointGroup d4 K := slSh σ hσ (sl2Lower c)

variable (K) in
noncomputable def W0 : adjointGroup d4 K := w4 2 1

variable (K) in
noncomputable def W1 : adjointGroup d4 K := w4 0 1 * w4 1 1 * w4 3 1

variable (μ : Kˣ)

noncomputable def fP2 (c : K) : adjointGroup d4 K := W0 K * fP1 σ hσ ((μ : K) * c) * (W0 K)⁻¹

noncomputable def fM2 (c : K) : adjointGroup d4 K :=
  W0 K * fM1 σ hσ (((μ⁻¹ : Kˣ) : K) * c) * (W0 K)⁻¹

noncomputable def fP3 (c : K) : adjointGroup d4 K := W1 K * fP2 σ hσ μ c * (W1 K)⁻¹

noncomputable def fM3 (c : K) : adjointGroup d4 K := W1 K * fM2 σ hσ μ c * (W1 K)⁻¹

def wSL2 (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  sl2Upper 1 * sl2Lower (-1) * sl2Upper 1

noncomputable def psiMat (F : Subfield K) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) K :=
  !![(g 0 0 : K), (μ : K) * (g 0 1 : K); ((μ⁻¹ : Kˣ) : K) * (g 1 0 : K), (g 1 1 : K)]

theorem psiMat_mul (F : Subfield K) (g h : Matrix.SpecialLinearGroup (Fin 2) F) :
    psiMat μ F (g * h) = psiMat μ F g * psiMat μ F h := by
  have hμ : (μ : K) * ((μ⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hμ' : (μ : K) ≠ 0 := Units.ne_zero μ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [psiMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | (field_simp; done) | (field_simp; ring1)

noncomputable def mu1 : Kˣ := Units.map σ.toMonoidHom μ

noncomputable def Nmu : adjointGroup d4 K :=
  w4 0 μ * w4 1 (mu1 σ μ) * w4 3 (mu1 σ (mu1 σ μ))

noncomputable def Wtil2 : adjointGroup d4 K := W0 K * Nmu σ μ * (W0 K)⁻¹

noncomputable def psiMu (F : Subfield K) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨psiMat μ F g, by
    have h := g.2
    rw [Matrix.det_fin_two] at h ⊢
    have hμ : (μ : K) * ((μ⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h' : ((g 0 0 * g 1 1 - g 0 1 * g 1 0 : F) : K) = 1 := by rw [h]; rfl
    push_cast at h'
    simp only [psiMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination h' - (g 0 1 : K) * (g 1 0 : K) * hμ⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [psiMat]
  map_mul' g h := by
    apply Subtype.ext
    exact psiMat_mul μ F g h

noncomputable def theta1 (F : Subfield K) : Matrix.SpecialLinearGroup (Fin 2) F →* adjointGroup d4 K :=
  (slSh σ hσ).comp (Matrix.SpecialLinearGroup.map F.subtype)

noncomputable def theta2 (F : Subfield K) : Matrix.SpecialLinearGroup (Fin 2) F →* adjointGroup d4 K :=
  (MulAut.conj (W0 K)).toMonoidHom.comp ((slSh σ hσ).comp (psiMu μ F))

end Defs

structure FrameHyp (σ : K →+* K) (F : Subfield K) (d μ : Kˣ) : Prop where
  sigma3 : ∀ c, σ (σ (σ c)) = c
  fixed : ∀ c ∈ F, σ c = c
  d3 : d ^ 3 = 1
  d_ne : d ≠ 1
  sd : σ (d : K) = d
  sm : (d : K) * σ (μ : K) = μ

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
