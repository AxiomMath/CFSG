module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalDefs
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalFrame
import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix QuadraticMap CFSG.Open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K]

private noncomputable def frameNonempty_modelBilin (K : Type) [Field K] (a : K) :
    LinearMap.BilinForm K (Idx → K) :=
  LinearMap.mk₂ K
    (fun u w => ∑ i : Fin 3,
      (u (.inl i) * w (.inl i) - u (.inl i) * w (.inr (.inl i)) +
        u (.inr (.inl i)) * w (.inr (.inl i))) +
      a * u (.inr (.inr ())) * w (.inr (.inr ())))
    (fun u₁ u₂ w => by
      simp only [Pi.add_apply, Fin.sum_univ_three]; ring)
    (fun c u w => by
      simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring)
    (fun u w₁ w₂ => by
      simp only [Pi.add_apply, Fin.sum_univ_three]; ring)
    (fun c u w => by
      simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]; ring)

private noncomputable def frameNonempty_Qm (K : Type) [Field K] : QuadraticForm K (Idx → K) :=
  (frameNonempty_modelBilin K 1).toQuadraticMap

private theorem frameNonempty_Qm_apply (v : Idx → K) :
    frameNonempty_Qm K v = modelQuad K 1 v := by
  simp only [frameNonempty_Qm, LinearMap.BilinMap.toQuadraticMap_apply,
    frameNonempty_modelBilin, LinearMap.mk₂_apply, modelQuad, Fin.sum_univ_three]
  ring

private theorem frameNonempty_polarBilin_apply (u w : Idx → K) :
    (polarBilin (frameNonempty_Qm K)) u w = modelPolar K 1 u w := by
  simp only [frameNonempty_Qm, LinearMap.BilinMap.polarBilin_toQuadraticMap,
    LinearMap.add_apply, LinearMap.flip_apply, frameNonempty_modelBilin, LinearMap.mk₂_apply,
    modelPolar, Fin.sum_univ_three]
  ring

private theorem frameNonempty_Qm_nondegenerate (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (polarBilin (frameNonempty_Qm K)).Nondegenerate := by
  constructor
  · intro u hu
    exact eq_zero_of_forall_modelPolar_eq_zero h2 h3 (a := 1) one_ne_zero fun w => by
      rw [← frameNonempty_polarBilin_apply]; exact hu w
  · intro w hw
    refine eq_zero_of_forall_modelPolar_eq_zero h2 h3 (a := 1) one_ne_zero fun u => ?_
    rw [← modelPolar_comm, ← frameNonempty_polarBilin_apply]
    exact hw u

private theorem frameNonempty_finrank : Module.finrank K (Idx → K) = 2 * 3 + 1 := by
  rw [Module.finrank_fintype_fun_eq_card]
  norm_num [Idx, Fintype.card_sum]

private def frameNonempty_scaleFun (μ1 μ2 : K) (w : Idx → K) : Idx → K := fun a =>
  match a with
  | .inl i => μ1 * w (.inl i) - μ2 * w (.inr (.inl i))
  | .inr (.inl i) => μ2 * w (.inl i) + (μ1 - μ2) * w (.inr (.inl i))
  | .inr (.inr ()) => w (.inr (.inr ()))

private def frameNonempty_scaleInv (d μ1 μ2 : K) (u : Idx → K) : Idx → K := fun a =>
  match a with
  | .inl i => d * ((μ1 - μ2) * u (.inl i) + μ2 * u (.inr (.inl i)))
  | .inr (.inl i) => d * (-(μ2) * u (.inl i) + μ1 * u (.inr (.inl i)))
  | .inr (.inr ()) => u (.inr (.inr ()))

private theorem frameNonempty_scale_left (d μ1 μ2 : K)
    (hmu : μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2 = d⁻¹) (hd : d ≠ 0) (x y : K) :
    d * ((μ1 - μ2) * (μ1 * x - μ2 * y) + μ2 * (μ2 * x + (μ1 - μ2) * y)) = x := by
  have h : (μ1 - μ2) * (μ1 * x - μ2 * y) + μ2 * (μ2 * x + (μ1 - μ2) * y) =
      (μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2) * x := by ring
  rw [h, hmu, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem frameNonempty_scale_right (d μ1 μ2 : K)
    (hmu : μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2 = d⁻¹) (hd : d ≠ 0) (x y : K) :
    d * (-(μ2) * (μ1 * x - μ2 * y) + μ1 * (μ2 * x + (μ1 - μ2) * y)) = y := by
  have h : -(μ2) * (μ1 * x - μ2 * y) + μ1 * (μ2 * x + (μ1 - μ2) * y) =
      (μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2) * y := by ring
  rw [h, hmu, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem frameNonempty_scale_left_inv (d μ1 μ2 : K)
    (hmu : μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2 = d⁻¹) (hd : d ≠ 0) (x y : K) :
    μ1 * (d * ((μ1 - μ2) * x + μ2 * y)) - μ2 * (d * (-(μ2) * x + μ1 * y)) = x := by
  have h : μ1 * (d * ((μ1 - μ2) * x + μ2 * y)) - μ2 * (d * (-(μ2) * x + μ1 * y)) =
      d * ((μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2) * x) := by ring
  rw [h, hmu, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem frameNonempty_scale_right_inv (d μ1 μ2 : K)
    (hmu : μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2 = d⁻¹) (hd : d ≠ 0) (x y : K) :
    μ2 * (d * ((μ1 - μ2) * x + μ2 * y)) + (μ1 - μ2) * (d * (-(μ2) * x + μ1 * y)) = y := by
  have h : μ2 * (d * ((μ1 - μ2) * x + μ2 * y)) + (μ1 - μ2) * (d * (-(μ2) * x + μ1 * y)) =
      d * ((μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2) * y) := by ring
  rw [h, hmu, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem frameNonempty_scale_norm (d μ1 μ2 : K)
    (hmu : μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2 = d⁻¹) (hd : d ≠ 0) (x y : K) :
    d * ((μ1 * x - μ2 * y) ^ 2 - (μ1 * x - μ2 * y) * (μ2 * x + (μ1 - μ2) * y) +
      (μ2 * x + (μ1 - μ2) * y) ^ 2) = x ^ 2 - x * y + y ^ 2 := by
  have h : (μ1 * x - μ2 * y) ^ 2 - (μ1 * x - μ2 * y) * (μ2 * x + (μ1 - μ2) * y) +
      (μ2 * x + (μ1 - μ2) * y) ^ 2 =
      (μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2) * (x ^ 2 - x * y + y ^ 2) := by ring
  rw [h, hmu, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

private theorem frameNonempty_scale_modelQuad (d μ1 μ2 : K)
    (hmu : μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2 = d⁻¹) (hd : d ≠ 0) (w : Idx → K) :
    d * modelQuad K 1 (frameNonempty_scaleFun μ1 μ2 w) = modelQuad K d w := by
  rw [modelQuad, modelQuad]
  simp only [frameNonempty_scaleFun]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => frameNonempty_scale_norm d μ1 μ2 hmu hd _ _
  · ring

private noncomputable def frameNonempty_planeScale (d μ1 μ2 : K)
    (hmu : μ1 ^ 2 - μ1 * μ2 + μ2 ^ 2 = d⁻¹) (hd : d ≠ 0) :
    (Idx → K) ≃ₗ[K] (Idx → K) where
  toFun := frameNonempty_scaleFun μ1 μ2
  invFun := frameNonempty_scaleInv d μ1 μ2
  left_inv w := by
    funext a
    rcases a with i | i | z
    · exact frameNonempty_scale_left d μ1 μ2 hmu hd _ _
    · exact frameNonempty_scale_right d μ1 μ2 hmu hd _ _
    · rfl
  right_inv u := by
    funext a
    rcases a with i | i | z
    · exact frameNonempty_scale_left_inv d μ1 μ2 hmu hd _ _
    · exact frameNonempty_scale_right_inv d μ1 μ2 hmu hd _ _
    · rfl
  map_add' u w := by
    funext a
    rcases a with i | i | z <;>
      simp only [frameNonempty_scaleFun, Pi.add_apply] <;> ring
  map_smul' c u := by
    funext a
    rcases a with i | i | z <;>
      simp only [frameNonempty_scaleFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;>
      ring

theorem Frame.nonempty [Finite K] (hK : ringChar K ≠ 2) (h3 : (3 : K) ≠ 0) :
    Nonempty (Frame K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨d, hd, ⟨e⟩⟩ :=
    CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd hK (frameNonempty_Qm K)
      (frameNonempty_Qm_nondegenerate h2 h3) (n := 3) frameNonempty_finrank
  obtain ⟨μ1, μ2, hmu⟩ := exists_planeNorm_eq hK h3 d⁻¹
  let L : (Idx → K) ≃ₗ[K] (Idx → K) := frameNonempty_planeScale d μ1 μ2 hmu hd
  have hL : ∀ w, d * modelQuad K 1 (L w) = modelQuad K d w :=
    fun w => frameNonempty_scale_modelQuad d μ1 μ2 hmu hd w
  let P : GL Idx K :=
    (toLinEquiv Idx K).symm (L.trans (e : (Idx → K) ≃ₗ[K] (Idx → K)))
  refine ⟨hK, h3, d, hd, P, ?_⟩
  intro w
  have hPw : ((P : GL Idx K) : Matrix Idx Idx K) *ᵥ w =
      (L.trans (e : (Idx → K) ≃ₗ[K] (Idx → K))) w := by
    dsimp only [P]
    rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
  rw [hPw, ← coe_quadOdd 3 K, LinearEquiv.trans_apply]
  change quadOdd 3 K (e (L w)) = modelQuad K d w
  rw [e.map_app, _root_.smul_apply, smul_eq_mul, frameNonempty_Qm_apply]
  exact hL w

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
