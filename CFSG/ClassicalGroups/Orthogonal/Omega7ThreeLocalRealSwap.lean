module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalFrame

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix

variable {K : Type} [Field K]

private def swapMap (K : Type) [Field K] (w : Idx → K) : Idx → K :=
  fun a =>
    match a with
    | .inl i => if i = 1 then -w (.inl 0) else w (.inl (Equiv.swap 0 1 i))
    | .inr (.inl i) => if i = 1 then -w (.inr (.inl 0)) else w (.inr (.inl (Equiv.swap 0 1 i)))
    | .inr (.inr _) => w (.inr (.inr ()))

private def negPlane0 (K : Type) [Field K] (w : Idx → K) : Idx → K :=
  fun a =>
    match a with
    | .inl i => if i = 0 then -w (.inl 0) else w (.inl i)
    | .inr (.inl i) => if i = 0 then -w (.inr (.inl 0)) else w (.inr (.inl i))
    | .inr (.inr _) => w (.inr (.inr ()))

private def pairSwap (K : Type) [Field K] (v : Idx → K) : Idx → K :=
  fun a =>
    match a with
    | .inl i => v (.inl (Equiv.swap 0 1 i))
    | .inr (.inl i) => v (.inr (.inl (Equiv.swap 0 1 i)))
    | .inr (.inr _) => v (.inr (.inr ()))

private def swapA (K : Type) [Field K] : Idx → K :=
  Pi.single (.inl 0) (1 : K) - Pi.single (.inl 1) (1 : K)

private def swapB (K : Type) [Field K] : Idx → K :=
  -Pi.single (.inl 0) (1 : K) - (2 : K) • Pi.single (.inr (.inl 0)) (1 : K) +
    Pi.single (.inl 1) (1 : K) + (2 : K) • Pi.single (.inr (.inl 1)) (1 : K)

private def swapX (K : Type) [Field K] (s t : K) : Idx → K :=
  s • Pi.single (.inl 0) (1 : K) + t • Pi.single (.inr (.inl 0)) (1 : K)

private def swapY (K : Type) [Field K] (s t : K) : Idx → K :=
  (2 * t - s) • Pi.single (.inl 0) (1 : K) + (t - 2 * s) • Pi.single (.inr (.inl 0)) (1 : K)

private theorem swapA_quad (F : Frame K) : modelQuad K F.a (swapA K) = 2 := by
  simp [swapA, modelQuad, Fin.sum_univ_three]
  ring

private theorem swapB_quad (F : Frame K) : modelQuad K F.a (swapB K) = 6 := by
  simp [swapB, modelQuad, Fin.sum_univ_three]
  ring

private theorem swapX_quad (F : Frame K) {s t : K} (hst : s ^ 2 - s * t + t ^ 2 = 2) :
    modelQuad K F.a (swapX K s t) = 2 := by
  simp [swapX, modelQuad, Fin.sum_univ_three]
  linear_combination hst

private theorem swapY_quad (F : Frame K) {s t : K} (hst : s ^ 2 - s * t + t ^ 2 = 2) :
    modelQuad K F.a (swapY K s t) = 6 := by
  simp [swapY, modelQuad, Fin.sum_univ_three]
  linear_combination 3 * hst

private theorem realized_swap_XY (F : Frame K) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = 2) (w : Idx → K) :
    modelRefl K F.a (swapX K s t) (modelRefl K F.a (swapY K s t) w) = negPlane0 K w := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero F.hK
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero h2 F.h3
  have hxr : ∀ x, modelRefl K F.a (swapX K s t) x =
      x - (modelPolar K F.a (swapX K s t) x / 2) • swapX K s t := by
    intro x; rw [modelRefl, swapX_quad F hst]
  have hyr : ∀ x, modelRefl K F.a (swapY K s t) x =
      x - (modelPolar K F.a (swapY K s t) x / 6) • swapY K s t := by
    intro x; rw [modelRefl, swapY_quad F hst]
  rw [hxr, hyr]
  funext a
  rcases a with i | i | u
  · fin_cases i
    · simp [negPlane0, modelPolar, swapX, swapY, Fin.sum_univ_three]
      field_simp [h2, h6]
      linear_combination (-12 * w (Sum.inl 0)) * hst
    all_goals simp [negPlane0, modelPolar, swapX, swapY, Fin.sum_univ_three]
  · fin_cases i
    · simp [negPlane0, modelPolar, swapX, swapY, Fin.sum_univ_three]
      field_simp [h2, h6]
      linear_combination (-12 * w (Sum.inr (Sum.inl 0))) * hst
    all_goals simp [negPlane0, modelPolar, swapX, swapY, Fin.sum_univ_three]
  · cases u
    simp [negPlane0, modelPolar, swapX, swapY, Fin.sum_univ_three]

private theorem realized_swap_AB (F : Frame K) (v : Idx → K) :
    modelRefl K F.a (swapA K) (modelRefl K F.a (swapB K) v) = pairSwap K v := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero F.hK
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero h2 F.h3
  have har : ∀ x, modelRefl K F.a (swapA K) x =
      x - (modelPolar K F.a (swapA K) x / 2) • swapA K := by
    intro x; rw [modelRefl, swapA_quad F]
  have hbr : ∀ x, modelRefl K F.a (swapB K) x =
      x - (modelPolar K F.a (swapB K) x / 6) • swapB K := by
    intro x; rw [modelRefl, swapB_quad F]
  rw [har, hbr]
  funext a
  rcases a with i | i | u
  · fin_cases i
    · simp [pairSwap, modelPolar, swapA, swapB, Fin.sum_univ_three]
      field_simp [h2, h6]
      ring
    · simp [pairSwap, modelPolar, swapA, swapB, Fin.sum_univ_three]
      field_simp [h2, h6]
      ring
    · simp [pairSwap, modelPolar, swapA, swapB, Fin.sum_univ_three, Equiv.swap_apply_def]
  · fin_cases i
    · simp [pairSwap, modelPolar, swapA, swapB, Fin.sum_univ_three]
      field_simp [h2, h6]
      ring
    · simp [pairSwap, modelPolar, swapA, swapB, Fin.sum_univ_three]
      field_simp [h2, h6]
      ring
    · simp [pairSwap, modelPolar, swapA, swapB, Fin.sum_univ_three, Equiv.swap_apply_def]
  · cases u
    simp [pairSwap, modelPolar, swapA, swapB, Fin.sum_univ_three]

private theorem realized_swap_reflGL_four_mulVec (F : Frame K) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = 2) (w : Idx → K) :
    ((F.reflGL (swapA K) * F.reflGL (swapB K) * F.reflGL (swapX K s t) *
      F.reflGL (swapY K s t) : GL Idx K) : Matrix Idx Idx K) *ᵥ w = swapMap K w := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero F.hK
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero h2 F.h3
  have ha : modelQuad K F.a (swapA K) ≠ 0 := by rw [swapA_quad F]; exact h2
  have hb : modelQuad K F.a (swapB K) ≠ 0 := by rw [swapB_quad F]; exact h6
  have hx : modelQuad K F.a (swapX K s t) ≠ 0 := by rw [swapX_quad F hst]; exact h2
  have hy : modelQuad K F.a (swapY K s t) ≠ 0 := by rw [swapY_quad F hst]; exact h6
  rw [Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.reflGL_mulVec hy, F.reflGL_mulVec hx,
    F.reflGL_mulVec hb, F.reflGL_mulVec ha]
  rw [realized_swap_XY F hst w, realized_swap_AB F (negPlane0 K w)]
  funext a
  rcases a with i | i | u
  · fin_cases i <;> simp [pairSwap, negPlane0, swapMap, Equiv.swap_apply_def]
  · fin_cases i <;> simp [pairSwap, negPlane0, swapMap, Equiv.swap_apply_def]
  · cases u
    simp [pairSwap, negPlane0, swapMap, Equiv.swap_apply_def]

private theorem realized_swap_swapMap_rot (v : F3Cube) (w : Idx → K) :
    swapMap K (rotMat K (Multiplicative.toAdd v) *ᵥ w) =
      rotMat K (Multiplicative.toAdd (Multiplicative.ofAdd fun i =>
        Multiplicative.toAdd v (Equiv.swap 0 1 i))) *ᵥ swapMap K w := by
  funext a
  rcases a with i | i | u
  · fin_cases i <;>
      simp [swapMap, rotMat_mulVec_inl, rotMat_mulVec_inr_inl, rotMat_mulVec_inr_inr,
        Equiv.swap_apply_def, Pi.smul_apply, smul_eq_mul] <;>
      ring
  · fin_cases i <;>
      simp [swapMap, rotMat_mulVec_inl, rotMat_mulVec_inr_inl, rotMat_mulVec_inr_inr,
        Equiv.swap_apply_def, Pi.smul_apply, smul_eq_mul] <;>
      ring
  · cases u
    simp [swapMap, rotMat_mulVec_inr_inr]

theorem realized_swap [Finite K] (F : Frame K) :
    Realized F (Equiv.swap 0 1) (fun _ => 1) := by
  obtain ⟨s, t, hst⟩ := exists_planeNorm_eq F.hK F.h3 (2 : K)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero F.hK
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero h2 F.h3
  have hmem : F.P * (F.reflGL (swapA K) * F.reflGL (swapB K) * F.reflGL (swapX K s t) *
      F.reflGL (swapY K s t)) * F.P⁻¹ ∈ Omega7 K :=
    F.mem_Omega7_conj_reflGL_four (a := swapA K) (b := swapB K) (x := swapX K s t)
      (y := swapY K s t)
      (by rw [swapA_quad F, swapX_quad F hst]) (by rw [swapA_quad F]; exact h2)
      (by rw [swapB_quad F, swapY_quad F hst]) (by rw [swapB_quad F]; exact h6)
  refine F.realized_of_model (Equiv.swap 0 1) (fun _ => 1) hmem fun v => ?_
  have hmat : ((F.reflGL (swapA K) * F.reflGL (swapB K) * F.reflGL (swapX K s t) *
      F.reflGL (swapY K s t) : GL Idx K) : Matrix Idx Idx K) *
        rotMat K (Multiplicative.toAdd v) =
      rotMat K (Multiplicative.toAdd (Multiplicative.ofAdd fun i =>
        Multiplicative.toAdd v (Equiv.swap 0 1 i))) *
      ((F.reflGL (swapA K) * F.reflGL (swapB K) * F.reflGL (swapX K s t) *
        F.reflGL (swapY K s t) : GL Idx K) : Matrix Idx Idx K) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, realized_swap_reflGL_four_mulVec F hst,
      realized_swap_reflGL_four_mulVec F hst]
    exact realized_swap_swapMap_rot v (Pi.single j 1)
  have h := conj_rotGL_eq_of_mul_eq (v := v) (v' := Multiplicative.ofAdd fun i =>
    Multiplicative.toAdd v (Equiv.swap 0 1 i)) hmat
  simpa only [one_mul] using h

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
