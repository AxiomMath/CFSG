module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthLevi
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open QuadraticMap Module Matrix

@[expose] def idSL (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    V →ₛₗ[((RingEquiv.refl K : K ≃+* K) : K →+* K)] V where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev HFrame {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (r : ℕ) :=
  Frame (σ := RingEquiv.refl K) Q (idSL K V) r

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [CharP K 2]
  {σ : K ≃+* K} {Q : QuadraticForm K V} {T : V →ₛₗ[(σ : K →+* K)] V} {r : ℕ}

theorem HFrame.coeffs_T_swap (hTQ : ∀ v, Q (T v) = σ (Q v)) (F : HFrame Q r)
    (hs : ∀ i, T (F.e i) = F.f i ∧ T (F.f i) = F.e i) (v : V) :
    F.coeffs (T v) = ((fun i => σ ((F.coeffs v).2 i)), (fun i => σ ((F.coeffs v).1 i))) := by
  rw [Frame.coeffs_apply, Frame.coeffs_apply]
  refine Prod.ext ?_ ?_ <;> funext i <;> simp only
  · rw [← (hs i).1, polar_semilinear T hTQ]
  · rw [← (hs i).2, polar_semilinear T hTQ]

theorem HFrame.T_expand_swap (F : HFrame Q r)
    (hs : ∀ i, T (F.e i) = F.f i ∧ T (F.f i) = F.e i) (a b : Fin r → K) :
    T (F.expand (a, b)) = F.expand ((fun i => σ (b i)), (fun i => σ (a i))) := by
  rw [Frame.expand_apply, Frame.expand_apply, map_add, map_sum, map_sum]
  simp only [map_smulₛₗ, RingHom.coe_coe, (hs _).1, (hs _).2]
  rw [add_comm]

theorem HFrame.T_levi_swap (hTQ : ∀ v, Q (T v) = σ (Q v)) (F : HFrame Q r)
    (hs : ∀ i, T (F.e i) = F.f i ∧ T (F.f i) = F.e i)
    (M M' : Matrix (Fin r) (Fin r) K) (v : V) :
    T (F.levi M M' v) = F.levi ((M'.map σ)ᵀ) ((M.map σ)ᵀ) (T v) := by
  rw [Frame.levi_apply, Frame.levi_apply, map_add, HFrame.coeffs_T_swap hTQ F hs]
  congr 1
  obtain ⟨a, b⟩ := F.coeffs v
  rw [blockDelta_apply]
  simp only
  rw [HFrame.T_expand_swap F hs]
  congr 1
  rw [blockDelta_apply]
  refine Prod.ext ?_ ?_ <;> funext i
  · simp only [Pi.sub_apply, map_sub, Matrix.transpose_transpose]
    have h := RingHom.map_mulVec (σ : K →+* K) M'ᵀ b i
    simp only [RingEquiv.coe_toRingHom, Function.comp_def, Matrix.transpose_map] at h
    rw [h]
  · simp only [Pi.sub_apply, map_sub, Matrix.transpose_transpose]
    have h := RingHom.map_mulVec (σ : K →+* K) M a i
    simp only [RingEquiv.coe_toRingHom, Function.comp_def] at h
    rw [h]

end

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
