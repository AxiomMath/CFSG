module

public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramComorphism
public import CFSG.LieType.AlgebraicGroups.TwistedOrbitSurjectivity

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv

variable {k : Type} [Field k] [IsAlgClosed k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

omit [IsAlgClosed k] in
theorem glCoord_smooth : Algebra.Smooth k (GLCoord k ι) := by
  let R := MvPolynomial (ι × ι) k
  let B := Localization.Away (matCoordDet k ι)
  have : Algebra.Smooth R B :=
    Algebra.Smooth.of_isLocalization_Away (matCoordDet k ι)
  have : Algebra.Smooth k R := inferInstance
  have : Algebra.Smooth k B := Algebra.Smooth.comp k R B
  exact Algebra.Smooth.of_equiv (glCoordEquivLocalization k ι).symm

omit [IsAlgClosed k] in
theorem frobCo_pointMul (p e : ℕ) [Fact p.Prime] [CharP k p]
    (y z : WithConv (GLCoord k ι →ₐ[k] k)) :
    toConv ((y * z).ofConv.comp (frobCo p e)) =
      toConv (y.ofConv.comp (frobCo p e)) * toConv (z.ofConv.comp (frobCo p e)) := by
  apply WithConv.ext
  refine GLCoord.algHom_ext k ι (fun i j => ?_) ?_
  · simp only [AlgHom.comp_apply, frobCo_glEntry, map_pow, convMul_glEntry]
    change (iterateFrobenius k p e) (∑ l, y.ofConv (glEntry k ι i l) *
      z.ofConv (glEntry k ι l j)) = _
    simp only [map_sum, map_mul, iterateFrobenius_def]
  · simp only [AlgHom.comp_apply, frobCo_glDetInv, map_pow, convMul_glDetInv, mul_pow]

set_option maxHeartbeats 800000 in
theorem gl_frobenius_lang (p e : ℕ) [Fact p.Prime] [CharP k p]
    (he : 1 ≤ e) (x : Matrix.GeneralLinearGroup ι k) :
    ∃ h : Matrix.GeneralLinearGroup ι k,
      x = h⁻¹ * Units.map ((iterateFrobenius k p e).mapMatrix.toMonoidHom) h := by
  have : Algebra.Smooth k (GLCoord k ι) := glCoord_smooth
  let σ : GLCoord k ι →ₐc[k] GLCoord k ι :=
    bialgHomOfPointMul (frobCo p e) (frobCo_pointMul p e)
  have hσ : (σ : GLCoord k ι →ₐ[k] GLCoord k ι) = frobCo p e :=
    coe_bialgHomOfPointMul _ _
  have hd : ∀ D ∈ tangentSpace k (GLCoord k ι) (Bialgebra.counitAlgHom k (GLCoord k ι)),
      D ∘ₗ ((σ : GLCoord k ι →ₐ[k] GLCoord k ι) ^ 1).toLinearMap = 0 := by
    intro D hD
    rw [pow_one, hσ]
    exact tangent_comp_frobCo p he hD
  obtain ⟨h, hh⟩ := exceptional_Lang_connected_twisted_orbit_surjectivity
    σ (le_refl 1) hd (glPointEquiv x)
  refine ⟨glPointEquiv.symm h, ?_⟩
  apply glPointEquiv.injective
  rw [map_mul, map_inv, glPointEquiv.apply_symm_apply]
  rw [hh]
  congr 1
  change toConv (h.ofConv.comp (σ : GLCoord k ι →ₐ[k] GLCoord k ι)) = _
  rw [hσ]
  apply WithConv.ext
  refine GLCoord.algHom_ext k ι (fun i j => ?_) ?_
  · simp [glPointEquiv, glPoint_glEntry, frobCo_glEntry,
      Matrix.map_apply, RingHom.mapMatrix_apply, iterateFrobenius_def, pointGL, pointMatrix]
  · simp [glPointEquiv, glPoint_glDetInv, frobCo_glDetInv]
    change h.ofConv (glDetInv k ι) ^ p ^ e =
      ((iterateFrobenius k p e).mapMatrix (pointMatrix h.ofConv)).det⁻¹
    rw [← RingHom.map_det, ← map_inv₀]
    change h.ofConv (glDetInv k ι) ^ p ^ e =
      (iterateFrobenius k p e) ((pointMatrix h.ofConv).det⁻¹)
    rw [inv_eq_of_mul_eq_one_right (det_pointMatrix_mul h.ofConv)]
    rfl

theorem gl_frobenius_inner_twist (p e : ℕ) [Fact p.Prime] [CharP k p]
    (he : 1 ≤ e) (g : Matrix.GeneralLinearGroup ι k) :
    ∃ h : Matrix.GeneralLinearGroup ι k, ∀ x : Matrix.GeneralLinearGroup ι k,
      g * Units.map ((iterateFrobenius k p e).mapMatrix.toMonoidHom) x * g⁻¹ =
        h⁻¹ * Units.map ((iterateFrobenius k p e).mapMatrix.toMonoidHom)
          (h * x * h⁻¹) * h := by
  obtain ⟨h, hh⟩ := gl_frobenius_lang p e he g
  let Φ : Matrix.GeneralLinearGroup ι k →* Matrix.GeneralLinearGroup ι k :=
    Units.map ((iterateFrobenius k p e).mapMatrix.toMonoidHom)
  change g = h⁻¹ * Φ h at hh
  refine ⟨h, fun x => ?_⟩
  change g * Φ x * g⁻¹ = h⁻¹ * Φ (h * x * h⁻¹) * h
  rw [map_mul, map_mul, map_inv, hh]
  group


end CFSG.LieType.AlgebraicGroups
