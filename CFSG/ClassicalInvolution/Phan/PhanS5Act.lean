module

public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

abbrev W7 (K : Type) : Type := Fin 3 ⊕ Fin 3 ⊕ Unit → K

section Ext

variable {F K : Type} [Field F] [Field K] [Algebra F K]

@[expose] def emb (x : W7 F) : W7 K := fun s => algebraMap F K (x s)

@[expose] noncomputable def extK (f : W7 F →ₗ[F] W7 F) : W7 K →ₗ[K] W7 K :=
  Matrix.mulVecLin ((LinearMap.toMatrix' f).map (algebraMap F K))

theorem extK_emb (f : W7 F →ₗ[F] W7 F) (x : W7 F) : extK (K := K) f (emb x) = emb (f x) := by
  funext s
  have h := RingHom.map_mulVec (algebraMap F K) (LinearMap.toMatrix' f) x s
  rw [LinearMap.toMatrix'_mulVec] at h
  simp only [extK, Matrix.mulVecLin_apply, emb]
  exact h.symm

theorem extK_comp (f g : W7 F →ₗ[F] W7 F) :
    extK (K := K) (f ∘ₗ g) = extK f ∘ₗ extK g := by
  simp only [extK, LinearMap.toMatrix'_comp, Matrix.map_mul (f := algebraMap F K),
    Matrix.mulVecLin_mul]

theorem extK_id : extK (K := K) (LinearMap.id : W7 F →ₗ[F] W7 F) = LinearMap.id := by
  simp only [extK, LinearMap.toMatrix'_id]
  ext x s
  simp

@[expose] def mapV (τ : K → K) (x : W7 K) : W7 K := fun s => τ (x s)

theorem extK_mapV (τ : K →+* K) (hτ : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a)
    (f : W7 F →ₗ[F] W7 F) (x : W7 K) : extK f (mapV τ x) = mapV τ (extK f x) := by
  funext s
  simp only [extK, mapV, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hτ]

end Ext

section Act

variable {F K : Type} [Field F] [Field K] [Algebra F K]

@[expose] noncomputable def actK (g : spinGroup (quadOdd 3 F)) : W7 K →ₗ[K] W7 K :=
  extK (spinAction (quadOdd 3 F) g).toLinearMap

theorem actK_emb (g : spinGroup (quadOdd 3 F)) (x : W7 F) :
    actK (K := K) g (emb x) = emb (spinAction (quadOdd 3 F) g x) :=
  extK_emb _ x

theorem actK_mul (g h : spinGroup (quadOdd 3 F)) (x : W7 K) :
    actK (g * h) x = actK g (actK h x) := by
  have : (spinAction (quadOdd 3 F) (g * h)).toLinearMap =
      (spinAction (quadOdd 3 F) g).toLinearMap ∘ₗ (spinAction (quadOdd 3 F) h).toLinearMap := by
    ext v
    simp
  simp only [actK, this, extK_comp, LinearMap.comp_apply]

theorem actK_one (x : W7 K) : actK (1 : spinGroup (quadOdd 3 F)) x = x := by
  have : (spinAction (quadOdd 3 F) 1).toLinearMap = LinearMap.id := by
    ext v
    simp
  simp only [actK, this, extK_id, LinearMap.id_apply]

theorem polar_emb (x y : W7 F) :
    polar (quadOdd 3 K) (emb x) (emb y) = algebraMap F K (polar (quadOdd 3 F) x y) := by
  simp only [polar_quadOdd, emb, map_add, map_mul, map_sum, map_ofNat]

theorem polar_actK (g : spinGroup (quadOdd 3 F)) (x y : W7 K) :
    polar (quadOdd 3 K) (actK g x) (actK g y) = polar (quadOdd 3 K) x y := by
  have hb : (polarBilin (quadOdd 3 K)).compl₁₂ (actK (K := K) g) (actK g) =
      polarBilin (quadOdd 3 K) := by
    refine LinearMap.BilinForm.ext_basis (Pi.basisFun K (Fin 3 ⊕ Fin 3 ⊕ Unit)) fun i j => ?_
    have hi : (Pi.basisFun K (Fin 3 ⊕ Fin 3 ⊕ Unit)) i =
        emb (K := K) (Pi.single i 1 : W7 F) := by
      funext s
      simp [emb, Pi.single_apply]
    have hj : (Pi.basisFun K (Fin 3 ⊕ Fin 3 ⊕ Unit)) j =
        emb (K := K) (Pi.single j 1 : W7 F) := by
      funext s
      simp [emb, Pi.single_apply]
    simp only [LinearMap.compl₁₂_apply, polarBilin_apply_apply, hi, hj, actK_emb, polar_emb,
      polar_spinAction]
  simpa using congrArg (fun B => B x y) hb

end Act

end CFSG.ClassicalInvolution.PhanB3.S
