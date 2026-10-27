module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFGForm
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Asc77.AscCX9X1
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.L4

open Matrix CFSG.ClassicalInvolution.Q3.TL4.Gauss
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm)

section Det

variable {F : Type} [Field F] [Finite F]

theorem det_eq_one_of_mul_self_eq_neg_one (hF : Nat.card F = 3)
    {A : Matrix (Fin 4) (Fin 4) F} (hA : A * A = -1) : A.det = 1 := by
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  let a : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) := LinearEquiv.ofLinearMap (Matrix.toLin' A)
    (Matrix.toLin' (-A))
    (by rw [← Matrix.toLin'_mul, Matrix.mul_neg, hA, neg_neg, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.neg_mul, hA, neg_neg, Matrix.toLin'_one])
  have happ : ∀ v, a v = A *ᵥ v := fun v => Matrix.toLin'_apply A v
  have ha : ∀ v, a (a v) = -v := fun v => by
    rw [happ, happ, mulVec_mulVec, hA, neg_mulVec, one_mulVec]
  let _ : Module (GaussField F) (Fin 4 → F) := gaussModule a ha
  have : IsScalarTower F (GaussField F) (Fin 4 → F) := ⟨fun c z v => by
    show (c • z).re • v + (c • z).im • a v = c • (z.re • v + z.im • a v)
    rw [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_add, smul_eq_mul, smul_eq_mul,
      mul_smul, mul_smul]⟩
  have hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v := fun v => by
    show (QuadraticAlgebra.omega : GaussField F).re • v +
      (QuadraticAlgebra.omega : GaussField F).im • a v = a v
    rw [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_smul, one_smul, zero_add]
  have : FiniteDimensional (GaussField F) (Fin 4 → F) :=
    Module.Finite.of_restrictScalars_finite F (GaussField F) (Fin 4 → F)
  have hfr : Module.finrank (GaussField F) (Fin 4 → F) = 2 := by
    have h := Module.finrank_mul_finrank F (GaussField F) (Fin 4 → F)
    rw [QuadraticAlgebra.finrank_eq_two, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at h
    omega
  set f : (Fin 4 → F) →ₗ[GaussField F] (Fin 4 → F) :=
    (QuadraticAlgebra.omega : GaussField F) • LinearMap.id with hf
  have hres : f.restrictScalars F = Matrix.toLin' A := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.restrictScalars_apply, hf, LinearMap.smul_apply, LinearMap.id_apply, hω,
      happ, Matrix.toLin'_apply]
  have hω2 : (QuadraticAlgebra.omega : GaussField F) ^ 2 = algebraMap F (GaussField F) (-1) := by
    ext <;> simp [sq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [← LinearMap.det_toLin', ← hres, LinearMap.det_restrictScalars, hf, LinearMap.det_smul,
    LinearMap.det_id, mul_one, hfr, hω2, Algebra.norm_algebraMap, QuadraticAlgebra.finrank_eq_two]
  norm_num

end Det

section Alt

variable {F : Type} [Field F]

theorem exists_spForm_basis (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 4) (Fin 4) F}
    (hAt : Aᵀ = -A) (hA : A.det ≠ 0) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, Pᵀ * A * P = spForm 1 1 := by
  classical
  set B := Matrix.toBilin' A with hB
  have hBapp : ∀ u v, B u v = u ⬝ᵥ (A *ᵥ v) := fun u v => Matrix.toBilin'_apply' A u v
  have hskew : ∀ u v, B u v = -B v u := fun u v => by
    rw [hBapp, hBapp, dotProduct_mulVec, ← mulVec_transpose, hAt, neg_mulVec, neg_dotProduct,
      dotProduct_comm]
  have hself : ∀ v, B v v = 0 := fun v => by
    have h := hskew v v
    have h3 : (2 : F) * B v v = 0 := by linear_combination h
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' A hA
  have hex : ∀ u : Fin 4 → F, u ≠ 0 → ∃ w, B u w = 1 := by
    intro u hu
    obtain ⟨w, hw⟩ : ∃ w, B u w ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (hnd.1 u hc)
    exact ⟨(B u w)⁻¹ • w, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩
  set e₁ : Fin 4 → F := Pi.single 0 1 with he₁
  have he₁0 : e₁ ≠ 0 := fun h => by
    have := congrFun h 0
    simp [he₁] at this
  obtain ⟨f₁, hef₁⟩ := hex e₁ he₁0
  set W := LinearMap.ker ((B e₁).prod (B f₁)) with hW
  have hWdim : 2 ≤ Module.finrank F W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ((B e₁).prod (B f₁))
    have h3 : Module.finrank F (LinearMap.range ((B e₁).prod (B f₁))) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range ((B e₁).prod (B f₁)))
      simpa using this
    rw [Module.finrank_fin_fun] at h1
    rw [← hW] at h1
    omega
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨⟨e₂, he₂W⟩, he₂0⟩ := exists_ne (0 : W)
  have he₂W' := he₂W
  rw [hW, LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at he₂W'
  obtain ⟨h1e₂', h2e₂'⟩ := he₂W'
  have h1e₂ : B e₁ e₂ = 0 := h1e₂'
  have h2e₂ : B f₁ e₂ = 0 := h2e₂'
  have he₂ne : e₂ ≠ 0 := fun h => he₂0 (Subtype.ext h)
  obtain ⟨g, hg⟩ := hex e₂ he₂ne
  set f₂ : Fin 4 → F := g - B e₁ g • f₁ + B f₁ g • e₁ with hf₂
  have hfe₁ : B f₁ e₁ = -1 := by rw [hskew, hef₁]
  have he₂e₁ : B e₂ e₁ = 0 := by rw [hskew, h1e₂, neg_zero]
  have he₂f₁ : B e₂ f₁ = 0 := by rw [hskew, h2e₂, neg_zero]
  have k1 : B e₁ f₂ = 0 := by
    simp only [hf₂, map_add, map_sub, map_smul, smul_eq_mul, hef₁, hself]
    ring
  have k2 : B f₁ f₂ = 0 := by
    simp only [hf₂, map_add, map_sub, map_smul, smul_eq_mul, hfe₁, hself]
    ring
  have k3 : B e₂ f₂ = 1 := by
    simp only [hf₂, map_add, map_sub, map_smul, smul_eq_mul, he₂e₁, he₂f₁, hg]
    ring
  set col : Fin 4 → Fin 4 → F := ![e₁, f₁, e₂, f₂] with hcol
  refine ⟨Matrix.of fun r c => col c r, ?_⟩
  have hent : ∀ c c', ((Matrix.of fun r c => col c r)ᵀ * A * Matrix.of fun r c => col c r) c c' =
      B (col c) (col c') := by
    intro c c'
    rw [hBapp]
    simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Matrix.of_apply,
      Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  have hf₁e₁ := hfe₁
  have hf₂e₁ : B f₂ e₁ = 0 := by rw [hskew, k1, neg_zero]
  have hf₂f₁ : B f₂ f₁ = 0 := by rw [hskew, k2, neg_zero]
  have hf₂e₂ : B f₂ e₂ = -1 := by rw [hskew, k3]
  have hf₁e₂ : B f₁ e₂ = 0 := h2e₂
  ext c c'
  rw [hent]
  fin_cases c <;> fin_cases c' <;>
    simp [hcol, spForm, hself, hef₁, hfe₁, h1e₂, h2e₂, he₂e₁, he₂f₁, k1, k2, k3, hf₂e₁, hf₂f₁,
      hf₂e₂]

end Alt

end CFSG.ClassicalInvolution.Q3.TL4.L4
