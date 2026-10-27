module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalFrame
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRootOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

private def signChangeU (i : Fin 3) (s t : K) : Idx → K :=
  vecOf K (Pi.single i s) (Pi.single i t) 0

private def signChangeZ : Idx → K :=
  vecOf K (fun _ => 0) (fun _ => 0) 1

private noncomputable def signChangeR2 (a s t : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1 - s * (2 * s - t) / a, -s * (2 * t - s) / a;
     -t * (2 * s - t) / a, 1 - t * (2 * t - s) / a]

private theorem signChange_modelQuad_u {i : Fin 3} {s t a : K}
    (hst : s ^ 2 - s * t + t ^ 2 = a) :
    modelQuad K a (signChangeU i s t) = a := by
  rw [signChangeU, modelQuad_vecOf]
  fin_cases i <;> simp [Pi.single_apply] <;> linear_combination hst

private theorem signChange_modelQuad_z (a : K) :
    modelQuad K a (signChangeZ (K := K)) = a := by
  rw [signChangeZ, modelQuad_vecOf]
  ring

private theorem signChange_modelPolar_u_vecOf (a : K) (i : Fin 3) (s t : K) (xs ys : Fin 3 → K)
    (z : K) :
    modelPolar K a (signChangeU i s t) (vecOf K xs ys z) =
      (2 * s - t) * xs i + (2 * t - s) * ys i := by
  rw [signChangeU, modelPolar_vecOf]
  fin_cases i <;> simp [Pi.single_apply] <;> ring

private theorem signChange_modelPolar_u (a : K) (i : Fin 3) (s t : K) (y : Idx → K) :
    modelPolar K a (signChangeU i s t) y =
      (2 * s - t) * y (.inl i) + (2 * t - s) * y (.inr (.inl i)) := by
  rw [← vecOf_eq_self y, signChange_modelPolar_u_vecOf]
  rfl

private noncomputable def signChangeR2num (a s t : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a - s * (2 * s - t), -s * (2 * t - s);
     -t * (2 * s - t), a - t * (2 * t - s)]

private theorem signChangeR2_eq_inv_smul {a s t : K} (ha : a ≠ 0) :
    signChangeR2 a s t = a⁻¹ • signChangeR2num a s t := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [signChangeR2, signChangeR2num, Matrix.smul_apply] <;>
    field_simp [ha] <;> ring

private theorem signChangeR2num_mul_planeRot {s t : K} (k : ZMod 3) :
    signChangeR2num (s ^ 2 - s * t + t ^ 2) s t * planeRot K k =
      planeRot K (-k) * signChangeR2num (s ^ 2 - s * t + t ^ 2) s t := by
  rcases zmod3_cases k with rfl | rfl | rfl
  · rw [show (-(0 : ZMod 3)) = 0 from by decide]; simp [planeRot_zero]
  · rw [show (-1 : ZMod 3) = 2 from by decide]
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [signChangeR2num, planeRot_one, planeRot_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring
  · rw [show (-2 : ZMod 3) = 1 from by decide]
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [signChangeR2num, planeRot_two, planeRot_one, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring

private theorem signChangeR2_mul_planeRot {a s t : K} (hst : s ^ 2 - s * t + t ^ 2 = a)
    (ha : a ≠ 0) (k : ZMod 3) :
    signChangeR2 a s t * planeRot K k = planeRot K (-k) * signChangeR2 a s t := by
  simp only [signChangeR2_eq_inv_smul ha]
  rw [← hst, Matrix.smul_mul, Matrix.mul_smul, signChangeR2num_mul_planeRot]

private theorem signChangeR2_mulVec_planeRot {a s t : K} (hst : s ^ 2 - s * t + t ^ 2 = a)
    (ha : a ≠ 0) (k : ZMod 3) (p : Fin 2 → K) :
    signChangeR2 a s t *ᵥ (planeRot K k *ᵥ p) =
      planeRot K (-k) *ᵥ (signChangeR2 a s t *ᵥ p) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, signChangeR2_mul_planeRot hst ha k]

private theorem signChange_modelRefl_z (F : Frame K) (x : Idx → K) :
    modelRefl K F.a (signChangeZ (K := K)) x =
      vecOf K (fun j => x (.inl j)) (fun j => x (.inr (.inl j)))
        (-(x (.inr (.inr ())))) := by
  have hq : modelQuad K F.a (signChangeZ (K := K)) = F.a := signChange_modelQuad_z F.a
  have hp : modelPolar K F.a (signChangeZ (K := K)) x = 2 * F.a * x (.inr (.inr ())) := by
    simp [modelPolar, signChangeZ, Fin.sum_univ_three]
  funext p
  rcases p with j | j | u
  · simp [modelRefl, hq, hp, signChangeZ]
  · simp [modelRefl, hq, hp, signChangeZ]
  · rw [Subsingleton.elim u ()]
    rw [modelRefl, hq, hp]
    simp only [Pi.sub_apply, Pi.smul_apply, signChangeZ, vecOf_inr_inr]
    field_simp [F.a_ne_zero]
    ring

private theorem signChange_modelRefl_z_comm (F : Frame K) (v : Fin 3 → ZMod 3) (x : Idx → K) :
    modelRefl K F.a (signChangeZ (K := K)) (rotMat K v *ᵥ x) =
      rotMat K v *ᵥ modelRefl K F.a (signChangeZ (K := K)) x := by
  rw [signChange_modelRefl_z F (rotMat K v *ᵥ x), signChange_modelRefl_z F x,
    rotMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext j; rw [rotMat_mulVec_inl]
  · ext j; rw [rotMat_mulVec_inr_inl]
  · rw [rotMat_mulVec_inr_inr]

private theorem signChange_modelRefl_u_inl (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (y : Idx → K) :
    modelRefl K F.a (signChangeU i s t) y (.inl i) =
      signChangeR2 F.a s t 0 0 * y (.inl i) +
        signChangeR2 F.a s t 0 1 * y (.inr (.inl i)) := by
  rw [modelRefl, signChange_modelQuad_u hst, signChange_modelPolar_u, Pi.sub_apply,
    Pi.smul_apply]
  simp [signChangeU, signChangeR2, Pi.single_apply]
  field_simp [F.a_ne_zero]
  ring

private theorem signChange_modelRefl_u_inr_inl (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (y : Idx → K) :
    modelRefl K F.a (signChangeU i s t) y (.inr (.inl i)) =
      signChangeR2 F.a s t 1 0 * y (.inl i) +
        signChangeR2 F.a s t 1 1 * y (.inr (.inl i)) := by
  rw [modelRefl, signChange_modelQuad_u hst, signChange_modelPolar_u, Pi.sub_apply,
    Pi.smul_apply]
  simp [signChangeU, signChangeR2, Pi.single_apply]
  field_simp [F.a_ne_zero]
  ring

private theorem signChange_modelRefl_u_inl_of_ne (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (y : Idx → K) {j : Fin 3} (hji : j ≠ i) :
    modelRefl K F.a (signChangeU i s t) y (.inl j) = y (.inl j) := by
  rw [modelRefl, signChange_modelQuad_u hst, signChange_modelPolar_u, Pi.sub_apply,
    Pi.smul_apply, signChangeU]
  simp [Pi.single_apply, hji]

private theorem signChange_modelRefl_u_inr_inl_of_ne (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (y : Idx → K) {j : Fin 3} (hji : j ≠ i) :
    modelRefl K F.a (signChangeU i s t) y (.inr (.inl j)) = y (.inr (.inl j)) := by
  rw [modelRefl, signChange_modelQuad_u hst, signChange_modelPolar_u, Pi.sub_apply,
    Pi.smul_apply, signChangeU]
  simp [Pi.single_apply, hji]

private theorem signChange_modelRefl_u_inr_inr (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (y : Idx → K) :
    modelRefl K F.a (signChangeU i s t) y (.inr (.inr ())) = y (.inr (.inr ())) := by
  rw [modelRefl, signChange_modelQuad_u hst, signChange_modelPolar_u, Pi.sub_apply,
    Pi.smul_apply, signChangeU]
  simp

private theorem signChange_modelRefl_u_plane (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (y : Idx → K) :
    ![modelRefl K F.a (signChangeU i s t) y (.inl i),
      modelRefl K F.a (signChangeU i s t) y (.inr (.inl i))] =
      signChangeR2 F.a s t *ᵥ ![y (.inl i), y (.inr (.inl i))] := by
  ext p
  fin_cases p <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, signChange_modelRefl_u_inl F i hst y,
      signChange_modelRefl_u_inr_inl F i hst y]

private theorem rotMat_plane (v : Fin 3 → ZMod 3) (y : Idx → K) (i : Fin 3) :
    ![(rotMat K v *ᵥ y) (.inl i), (rotMat K v *ᵥ y) (.inr (.inl i))] =
      planeRot K (v i) *ᵥ ![y (.inl i), y (.inr (.inl i))] := by
  ext p
  fin_cases p
  · rw [rotMat_mulVec_inl]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [rotMat_mulVec_inr_inl]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem signChange_refl_u_conj (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (v : Fin 3 → ZMod 3) (y : Idx → K) :
    modelRefl K F.a (signChangeU i s t) (rotMat K v *ᵥ y) =
      rotMat K (fun j => (if j = i then -1 else 1) * v j) *ᵥ
        modelRefl K F.a (signChangeU i s t) y := by
  have hplane :
      ![modelRefl K F.a (signChangeU i s t) (rotMat K v *ᵥ y) (.inl i),
        modelRefl K F.a (signChangeU i s t) (rotMat K v *ᵥ y) (.inr (.inl i))] =
      ![ (rotMat K (fun j => (if j = i then -1 else 1) * v j) *ᵥ
            modelRefl K F.a (signChangeU i s t) y) (.inl i),
         (rotMat K (fun j => (if j = i then -1 else 1) * v j) *ᵥ
            modelRefl K F.a (signChangeU i s t) y) (.inr (.inl i))] := by
    conv_lhs =>
      rw [signChange_modelRefl_u_plane F i hst (rotMat K v *ᵥ y), rotMat_plane v y i,
        signChangeR2_mulVec_planeRot hst F.a_ne_zero (v i) ![y (.inl i), y (.inr (.inl i))]]
    conv_rhs =>
      rw [rotMat_plane (fun j => (if j = i then -1 else 1) * v j)
          (modelRefl K F.a (signChangeU i s t) y) i,
        signChange_modelRefl_u_plane F i hst y]
    congr 1
    congr 1
    rw [if_pos rfl]
    exact (neg_one_mul (v i)).symm
  funext p
  rcases p with j | j | u
  · by_cases h : j = i
    · subst h
      exact congrFun hplane 0
    · rw [signChange_modelRefl_u_inl_of_ne F i hst (rotMat K v *ᵥ y) h, rotMat_mulVec_inl,
        rotMat_mulVec_inl, signChange_modelRefl_u_inl_of_ne F i hst y h,
        signChange_modelRefl_u_inr_inl_of_ne F i hst y h]
      simp [h]
  · by_cases h : j = i
    · subst h
      exact congrFun hplane 1
    · rw [signChange_modelRefl_u_inr_inl_of_ne F i hst (rotMat K v *ᵥ y) h,
        rotMat_mulVec_inr_inl, rotMat_mulVec_inr_inl,
        signChange_modelRefl_u_inl_of_ne F i hst y h,
        signChange_modelRefl_u_inr_inl_of_ne F i hst y h]
      simp [h]
  · rw [Subsingleton.elim u (), signChange_modelRefl_u_inr_inr F i hst (rotMat K v *ᵥ y),
      rotMat_mulVec_inr_inr, rotMat_mulVec_inr_inr, signChange_modelRefl_u_inr_inr F i hst y]

private theorem signChange_conj_rotMat (F : Frame K) (i : Fin 3) {s t : K}
    (hst : s ^ 2 - s * t + t ^ 2 = F.a) (v : Fin 3 → ZMod 3) :
    ((F.reflGL (signChangeU i s t) * F.reflGL (signChangeZ (K := K)) : GL Idx K) :
        Matrix Idx Idx K) * rotMat K v =
      rotMat K (fun j => (if j = i then -1 else 1) * v j) *
        ((F.reflGL (signChangeU i s t) * F.reflGL (signChangeZ (K := K)) : GL Idx K) :
          Matrix Idx Idx K) := by
  have hu : modelQuad K F.a (signChangeU i s t) ≠ 0 := by
    rw [signChange_modelQuad_u hst]; exact F.a_ne_zero
  have hd : modelQuad K F.a (signChangeZ (K := K)) ≠ 0 := by
    rw [signChange_modelQuad_z]; exact F.a_ne_zero
  rw [Matrix.ext_iff_mulVec]
  intro x
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, F.reflGL_mulVec hu, F.reflGL_mulVec hd]
  rw [signChange_modelRefl_z_comm F v x]
  exact signChange_refl_u_conj F i hst v (modelRefl K F.a (signChangeZ (K := K)) x)

theorem realized_signChange [Finite K] (F : Frame K) (i : Fin 3) :
    Realized F 1 (fun j => if j = i then -1 else 1) := by
  obtain ⟨s, t, hst⟩ := exists_planeNorm_eq F.hK F.h3 F.a
  have hu : modelQuad K F.a (signChangeU i s t) ≠ 0 := by
    rw [signChange_modelQuad_u hst]; exact F.a_ne_zero
  have hQ : modelQuad K F.a (signChangeU i s t) = modelQuad K F.a (signChangeZ (K := K)) := by
    rw [signChange_modelQuad_u hst, signChange_modelQuad_z]
  have hmem := F.mem_Omega7_conj_reflGL_mul hQ hu
  refine F.realized_of_model 1 (fun j => if j = i then -1 else 1) hmem ?_
  intro v
  have h := conj_rotGL_eq_of_mul_eq
    (m := F.reflGL (signChangeU i s t) * F.reflGL (signChangeZ (K := K)))
    (v := v)
    (v' := Multiplicative.ofAdd fun j => (if j = i then -1 else 1) * Multiplicative.toAdd v j)
    (signChange_conj_rotMat F i hst (Multiplicative.toAdd v))
  simpa using h

private def cycleLiftPerm : Equiv.Perm Idx :=
  Equiv.sumCongr (finRotate 3) (Equiv.sumCongr (finRotate 3) (Equiv.refl Unit))

private noncomputable def cyclePermGL (K : Type) [Field K] : GL Idx K :=
  ⟨cycleLiftPerm.permMatrix K, cycleLiftPerm⁻¹.permMatrix K, by
    rw [← permMatrix_mul (σ := cycleLiftPerm⁻¹) (τ := cycleLiftPerm), inv_mul_cancel,
      Matrix.permMatrix_one], by
    rw [← permMatrix_mul (σ := cycleLiftPerm) (τ := cycleLiftPerm⁻¹), mul_inv_cancel,
      Matrix.permMatrix_one]⟩

private theorem cyclePermGL_mulVec_vecOf (xs ys : Fin 3 → K) (z : K) :
    (cyclePermGL K : Matrix Idx Idx K) *ᵥ vecOf K xs ys z =
      vecOf K (fun i => xs (finRotate 3 i)) (fun i => ys (finRotate 3 i)) z := by
  change cycleLiftPerm.permMatrix K *ᵥ vecOf K xs ys z = _
  rw [permMatrix_mulVec]
  funext p
  rcases p with i | i | u
  · simp [cycleLiftPerm]
  · simp [cycleLiftPerm]
  · rw [Subsingleton.elim u ()]
    simp [cycleLiftPerm]

private theorem cycleLiftPerm_pow_three : cycleLiftPerm ^ 3 = 1 := by decide

private theorem cyclePermGL_pow_three : cyclePermGL K ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  show (cycleLiftPerm.permMatrix K) ^ 3 = 1
  rw [pow_succ, pow_two,
    ← permMatrix_mul (σ := cycleLiftPerm) (τ := cycleLiftPerm),
    ← permMatrix_mul (σ := cycleLiftPerm) (τ := cycleLiftPerm * cycleLiftPerm),
    show cycleLiftPerm * (cycleLiftPerm * cycleLiftPerm) = cycleLiftPerm ^ 3 by
      rw [pow_succ, pow_two, mul_assoc],
    cycleLiftPerm_pow_three, Matrix.permMatrix_one]

private theorem cyclePermGL_isometry_vecOf (a : K) (xs ys : Fin 3 → K) (z : K) :
    modelQuad K a ((cyclePermGL K : Matrix Idx Idx K) *ᵥ vecOf K xs ys z) =
      modelQuad K a (vecOf K xs ys z) := by
  rw [cyclePermGL_mulVec_vecOf, modelQuad_vecOf, modelQuad_vecOf]
  have h0 : finRotate 3 0 = 1 := by decide
  have h1 : finRotate 3 1 = 2 := by decide
  have h2 : finRotate 3 2 = 0 := by decide
  rw [h0, h1, h2]
  ring

private theorem cyclePermGL_isometry (a : K) (w : Idx → K) :
    modelQuad K a ((cyclePermGL K : Matrix Idx Idx K) *ᵥ w) = modelQuad K a w := by
  conv_lhs => rw [← vecOf_eq_self w]
  conv_rhs => rw [← vecOf_eq_self w]
  exact cyclePermGL_isometry_vecOf a _ _ _

private theorem cyclePermGL_conj_rotMat (v : Fin 3 → ZMod 3) :
    (cyclePermGL K : Matrix Idx Idx K) * rotMat K v =
      rotMat K (fun i => v (finRotate 3 i)) * cyclePermGL K := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  conv_lhs =>
    rw [← vecOf_eq_self x, ← Matrix.mulVec_mulVec, rotMat_mulVec_vecOf,
      cyclePermGL_mulVec_vecOf]
  conv_rhs =>
    rw [← vecOf_eq_self x, ← Matrix.mulVec_mulVec, cyclePermGL_mulVec_vecOf,
      rotMat_mulVec_vecOf]

theorem realized_cycle [Finite K] (F : Frame K) :
    Realized F (finRotate 3) (fun _ => 1) := by
  have hodd : Odd (orderOf (cyclePermGL K)) :=
    Odd.of_dvd_nat (by decide : Odd 3)
      (orderOf_dvd_of_pow_eq_one (cyclePermGL_pow_three (K := K)))
  have hmem := F.mem_Omega7_conj_of_odd (cyclePermGL_isometry F.a) hodd
  refine F.realized_of_model (finRotate 3) (fun _ => 1) hmem ?_
  intro v
  have h := conj_rotGL_eq_of_mul_eq
    (m := cyclePermGL K) (v := v)
    (v' := Multiplicative.ofAdd fun i => 1 * Multiplicative.toAdd v (finRotate 3 i))
    (by simpa using cyclePermGL_conj_rotMat (K := K) (Multiplicative.toAdd v))
  simpa using h

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
