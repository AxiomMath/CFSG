module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Matrix CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open CFSG.RankThree.PartOne.KCAlternating (IsSymplecticBasis IsSymplecticBasis.toMatrix_eq)

variable {K : Type} [Field K] {U : Type*} [AddCommGroup U] [Module K U]

theorem toMatrix_transpose_mul_J_mul {r : ℕ} {β : BilinForm K U} (hβ : β.IsAlt)
    {b : Basis (Fin r ⊕ Fin r) K U} (hb : IsSymplecticBasis β b) {f : U →ₗ[K] U}
    (hf : ∀ u u', β (f u) (f u') = β u u') :
    (LinearMap.toMatrix b b f)ᵀ * fromBlocks 0 1 (-1) 0 * LinearMap.toMatrix b b f =
      fromBlocks 0 1 (-1) 0 := by
  have hcomp : β.comp f f = β := by
    ext u u'
    exact hf u u'
  have h := LinearMap.BilinForm.toMatrix_comp b b β f f
  rw [hcomp, hb.toMatrix_eq hβ] at h
  exact h.symm

theorem toLin_isometry_of_mem {r : ℕ} {β : BilinForm K U} (hβ : β.IsAlt)
    {b : Basis (Fin r ⊕ Fin r) K U} (hb : IsSymplecticBasis β b)
    {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hA : Aᵀ * fromBlocks 0 1 (-1) 0 * A = fromBlocks 0 1 (-1) 0) (u u' : U) :
    β (Matrix.toLin b b A u) (Matrix.toLin b b A u') = β u u' := by
  have h := LinearMap.BilinForm.toMatrix_comp b b β (Matrix.toLin b b A) (Matrix.toLin b b A)
  rw [LinearMap.toMatrix_toLin, hb.toMatrix_eq hβ, hA, ← hb.toMatrix_eq hβ] at h
  have h' := (LinearMap.BilinForm.toMatrix b).injective h
  exact congrArg (fun B : BilinForm K U => B u u') h'

variable {X : Type*} [Group X] {r : ℕ} {β : BilinForm K U} (hβ : β.IsAlt)
  {b : Basis (Fin r ⊕ Fin r) K U} (hb : IsSymplecticBasis β b) (φ : X →* Module.End K U)
  (hφ : ∀ x u u', β (φ x u) (φ x u') = β u u')

@[expose] noncomputable def sympChartGL (x : X) : GL (Fin r ⊕ Fin r) K where
  val := LinearMap.toMatrix b b (φ x)
  inv := LinearMap.toMatrix b b (φ x⁻¹)
  val_inv := by rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one,
    LinearMap.toMatrix_one]
  inv_val := by rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one,
    LinearMap.toMatrix_one]

@[expose] noncomputable def sympChart : X →* StatedSp r K where
  toFun x := ⟨sympChartGL (b := b) φ x, Subgroup.subset_closure
    (toMatrix_transpose_mul_J_mul hβ hb (hφ x))⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change LinearMap.toMatrix b b (φ 1) = 1
    rw [map_one, LinearMap.toMatrix_one]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    change LinearMap.toMatrix b b (φ (x * y)) =
      LinearMap.toMatrix b b (φ x) * LinearMap.toMatrix b b (φ y)
    rw [map_mul, LinearMap.toMatrix_mul]

theorem coe_sympChart (x : X) :
    (((sympChart hβ hb φ hφ x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = LinearMap.toMatrix b b (φ x) :=
  rfl

theorem sympChart_ker : (sympChart hβ hb φ hφ).ker = φ.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg (fun g : StatedSp r K =>
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h
    simp only [coe_sympChart, OneMemClass.coe_one, Units.val_one] at h'
    rw [← LinearMap.toMatrix_one b] at h'
    exact (LinearMap.toMatrix b b).injective h'
  · intro h
    apply Subtype.ext
    apply Units.ext
    rw [coe_sympChart, h, LinearMap.toMatrix_one]
    rfl

theorem spMatTrace_sympChart [Module.Finite K U] (x : X) :
    spMatTrace (sympChart hβ hb φ hφ x) = LinearMap.trace K U (φ x) := by
  rw [spMatTrace, coe_sympChart, LinearMap.trace_eq_matrix_trace K b]

theorem sympChart_surjective
    (hsurj : ∀ f : U →ₗ[K] U, (∀ u u', β (f u) (f u') = β u u') → ∃ x, φ x = f) :
    Function.Surjective (sympChart hβ hb φ hφ) := by
  intro g
  have hg : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      fromBlocks 0 1 (-1) 0 * ((g : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = fromBlocks 0 1 (-1) 0 := by
    have h1 : (g : GL (Fin r ⊕ Fin r) K) ∈ TauCeti.GLSymplectic (Fin r) K :=
      CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := K) ▸ g.2
    rw [TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup] at h1
    exact (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mpr h1
  obtain ⟨x, hx⟩ := hsurj _ (toLin_isometry_of_mem hβ hb hg)
  refine ⟨x, Subtype.ext (Units.ext ?_)⟩
  rw [coe_sympChart, hx, LinearMap.toMatrix_toLin]

end CFSG.SeitzReduction.OmegaPilot
