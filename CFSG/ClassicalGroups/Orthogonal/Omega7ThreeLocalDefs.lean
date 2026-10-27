module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaOddOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

abbrev Idx : Type := Fin 3 ⊕ Fin 3 ⊕ Unit

abbrev Omega7 (K : Type) [Field K] : Subgroup (GL Idx K) :=
  StatedOmega (StatedQuadOdd 3 K)

abbrev F3Cube : Type := Multiplicative (Fin 3 → ZMod 3)

@[expose] def modelQuad (K : Type) [Field K] (a : K) (w : Idx → K) : K :=
  ∑ i : Fin 3, (w (.inl i) ^ 2 - w (.inl i) * w (.inr (.inl i)) + w (.inr (.inl i)) ^ 2) +
    a * w (.inr (.inr ())) ^ 2

@[expose] def cubeRootMat (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

@[expose] def planeRot (K : Type) [Field K] (k : ZMod 3) : Matrix (Fin 2) (Fin 2) K :=
  cubeRootMat K ^ k.val

@[expose] def rotMat (K : Type) [Field K] (v : Fin 3 → ZMod 3) : Matrix Idx Idx K :=
  Matrix.of fun a b =>
    match a, b with
    | .inl i, .inl j => if i = j then planeRot K (v i) 0 0 else 0
    | .inl i, .inr (.inl j) => if i = j then planeRot K (v i) 0 1 else 0
    | .inr (.inl i), .inl j => if i = j then planeRot K (v i) 1 0 else 0
    | .inr (.inl i), .inr (.inl j) => if i = j then planeRot K (v i) 1 1 else 0
    | .inr (.inr _), .inr (.inr _) => 1
    | _, _ => 0

variable {K : Type} [Field K]

theorem cubeRootMat_pow_three : cubeRootMat K ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeRootMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem planeRot_add (a b : ZMod 3) : planeRot K (a + b) = planeRot K a * planeRot K b := by
  unfold planeRot
  rw [← pow_add, ZMod.val_add]
  exact (pow_eq_pow_mod _ cubeRootMat_pow_three).symm

theorem planeRot_zero : planeRot K 0 = 1 := by
  simp [planeRot]

theorem rotMat_zero : rotMat K 0 = 1 := by
  ext a b
  rcases a with i | i | u <;> rcases b with j | j | w <;>
    simp [rotMat, planeRot_zero, Matrix.one_apply]

theorem rotMat_add (v v' : Fin 3 → ZMod 3) : rotMat K (v + v') = rotMat K v * rotMat K v' := by
  ext a b
  rcases a with i | i | u <;> rcases b with j | j | w <;>
    simp [rotMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, planeRot_add,
      Fin.sum_univ_two] <;>
    (by_cases h : i = j <;> simp [h])

@[expose] def rotHom (K : Type) [Field K] : F3Cube →* Matrix Idx Idx K where
  toFun v := rotMat K (Multiplicative.toAdd v)
  map_one' := rotMat_zero
  map_mul' v v' := rotMat_add _ _

@[expose] def rotGL (K : Type) [Field K] : F3Cube →* GL Idx K :=
  (rotHom K).toHomUnits

structure Frame (K : Type) [Field K] where
  hK : ringChar K ≠ 2
  h3 : (3 : K) ≠ 0
  a : K
  a_ne_zero : a ≠ 0
  P : GL Idx K
  isometry : ∀ w, StatedQuadOdd 3 K ((P : Matrix Idx Idx K) *ᵥ w) = modelQuad K a w

@[expose] def c₀GL (F : Frame K) : F3Cube →* GL Idx K :=
  (MulAut.conj F.P).toMonoidHom.comp (rotGL K)

theorem planeRot_one : planeRot K 1 = !![0, -1; 1, -1] := by
  unfold planeRot
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
  rfl

theorem planeRot_two : planeRot K 2 = !![-1, 1; -1, 0] := by
  unfold planeRot
  rw [show (2 : ZMod 3).val = 2 from rfl, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubeRootMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem zmod3_cases (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k; decide

theorem rotMat_mulVec_inl (v : Fin 3 → ZMod 3) (w : Idx → K) (i : Fin 3) :
    (rotMat K v *ᵥ w) (.inl i) =
      planeRot K (v i) 0 0 * w (.inl i) + planeRot K (v i) 0 1 * w (.inr (.inl i)) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rotMat]

theorem rotMat_mulVec_inr_inl (v : Fin 3 → ZMod 3) (w : Idx → K) (i : Fin 3) :
    (rotMat K v *ᵥ w) (.inr (.inl i)) =
      planeRot K (v i) 1 0 * w (.inl i) + planeRot K (v i) 1 1 * w (.inr (.inl i)) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rotMat]

theorem rotMat_mulVec_inr_inr (v : Fin 3 → ZMod 3) (w : Idx → K) :
    (rotMat K v *ᵥ w) (.inr (.inr ())) = w (.inr (.inr ())) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rotMat]

theorem modelQuad_rotMat_mulVec (a : K) (v : Fin 3 → ZMod 3) (w : Idx → K) :
    modelQuad K a (rotMat K v *ᵥ w) = modelQuad K a w := by
  simp only [modelQuad, rotMat_mulVec_inl, rotMat_mulVec_inr_inl, rotMat_mulVec_inr_inr]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases zmod3_cases (v i) with h | h | h <;>
    simp [h, planeRot_zero, planeRot_one, planeRot_two] <;> ring

theorem c₀GL_coe (F : Frame K) (v : F3Cube) :
    ((c₀GL F v : GL Idx K) : Matrix Idx Idx K) =
      (F.P : Matrix Idx Idx K) * rotMat K (Multiplicative.toAdd v) *
        ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) := rfl

theorem c₀GL_isometry (F : Frame K) (v : F3Cube) (w : Idx → K) :
    StatedQuadOdd 3 K (((c₀GL F v : GL Idx K) : Matrix Idx Idx K) *ᵥ w) =
      StatedQuadOdd 3 K w := by
  rw [c₀GL_coe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.isometry,
    modelQuad_rotMat_mulVec, ← F.isometry, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

theorem F3Cube_pow_three (v : F3Cube) : v ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  have h : ∀ x : ZMod 3, 3 • x = 0 := by decide
  simpa [toAdd_pow] using h (Multiplicative.toAdd v i)

theorem c₀GL_pow_three (F : Frame K) (v : F3Cube) : c₀GL F v ^ 3 = 1 := by
  rw [← map_pow, F3Cube_pow_three, map_one]

theorem c₀GL_mem [Finite K] (F : Frame K) (v : F3Cube) : c₀GL F v ∈ Omega7 K := by
  refine CFSG.ClassicalGroups.Orthogonal.mem_statedOmega_quadOdd_of_odd F.hK _
    (c₀GL_isometry F v) ?_
  exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (c₀GL_pow_three F v))

@[expose] def c₀ [Finite K] (F : Frame K) : F3Cube →* ↥(Omega7 K) :=
  (c₀GL F).codRestrict (Omega7 K) (c₀GL_mem F)

theorem coe_c₀ [Finite K] (F : Frame K) (v : F3Cube) :
    ((c₀ F v : ↥(Omega7 K)) : GL Idx K) = c₀GL F v := rfl

theorem planeRot_injective {k k' : ZMod 3} (h : planeRot K k = planeRot K k') : k = k' := by
  have h00 := congr_fun (congr_fun h 0) 0
  have h10 := congr_fun (congr_fun h 1) 0
  have hz : (0 : K) ≠ -1 := by simp
  have hz' : (-1 : K) ≠ 0 := by simp
  rcases zmod3_cases k with rfl | rfl | rfl <;> rcases zmod3_cases k' with rfl | rfl | rfl <;>
    simp [planeRot_zero, planeRot_one, planeRot_two] at h00 h10 ⊢ <;> tauto

theorem c₀GL_injective (F : Frame K) : Function.Injective (c₀GL F) := by
  intro v v' h
  have h1 : rotGL K v = rotGL K v' := by
    have := h
    simp only [c₀GL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    exact mul_left_cancel (mul_right_cancel this)
  have h2 : rotMat K (Multiplicative.toAdd v) = rotMat K (Multiplicative.toAdd v') :=
    congrArg (fun g : GL Idx K => (g : Matrix Idx Idx K)) h1
  apply Multiplicative.toAdd.injective
  funext i
  have h3 : planeRot K (Multiplicative.toAdd v i) = planeRot K (Multiplicative.toAdd v' i) := by
    ext a b
    fin_cases a <;> fin_cases b
    · simpa [rotMat] using congr_fun (congr_fun h2 (.inl i)) (.inl i)
    · simpa [rotMat] using congr_fun (congr_fun h2 (.inl i)) (.inr (.inl i))
    · simpa [rotMat] using congr_fun (congr_fun h2 (.inr (.inl i))) (.inl i)
    · simpa [rotMat] using congr_fun (congr_fun h2 (.inr (.inl i))) (.inr (.inl i))
  exact planeRot_injective h3

theorem c₀_injective [Finite K] (F : Frame K) : Function.Injective (c₀ F) := fun v v' h =>
  c₀GL_injective F (congrArg Subtype.val h)

theorem plane_fixed_iff (h3 : (3 : K) ≠ 0) {k : ZMod 3} (hk : k ≠ 0) (x y : K) :
    (planeRot K k 0 0 * x + planeRot K k 0 1 * y = x ∧
      planeRot K k 1 0 * x + planeRot K k 1 1 * y = y) ↔ x = 0 ∧ y = 0 := by
  constructor
  · rcases zmod3_cases k with rfl | rfl | rfl
    · exact absurd rfl hk
    · simp only [planeRot_one]
      simp
      rintro h1 h2
      have hy : 3 * y = 0 := by linear_combination -h1 - h2
      have hy0 : y = 0 := by simpa [h3] using hy
      refine ⟨?_, hy0⟩
      rw [hy0] at h1
      linear_combination -h1
    · simp only [planeRot_two]
      simp
      rintro h1 h2
      have hx : 3 * x = 0 := by linear_combination -h1 - h2
      have hx0 : x = 0 := by simpa [h3] using hx
      refine ⟨hx0, ?_⟩
      rw [hx0] at h2
      linear_combination -h2
  · rintro ⟨rfl, rfl⟩
    simp

theorem rotMat_mulVec_eq_self_iff (h3 : (3 : K) ≠ 0) (v : Fin 3 → ZMod 3) (w : Idx → K) :
    rotMat K v *ᵥ w = w ↔ ∀ i, v i ≠ 0 → w (.inl i) = 0 ∧ w (.inr (.inl i)) = 0 := by
  constructor
  · intro h i hi
    have h1 := congr_fun h (.inl i)
    have h2 := congr_fun h (.inr (.inl i))
    rw [rotMat_mulVec_inl] at h1
    rw [rotMat_mulVec_inr_inl] at h2
    exact (plane_fixed_iff h3 hi _ _).1 ⟨h1, h2⟩
  · intro h
    funext a
    rcases a with i | i | u
    · rw [rotMat_mulVec_inl]
      by_cases hi : v i = 0
      · simp [hi, planeRot_zero]
      · obtain ⟨hx, hy⟩ := h i hi
        simp [hx, hy]
    · rw [rotMat_mulVec_inr_inl]
      by_cases hi : v i = 0
      · simp [hi, planeRot_zero]
      · obtain ⟨hx, hy⟩ := h i hi
        simp [hx, hy]
    · rw [rotMat_mulVec_inr_inr]

theorem c₀GL_mulVec_eq_self_iff (F : Frame K) (v : F3Cube) (w : Idx → K) :
    ((c₀GL F v : GL Idx K) : Matrix Idx Idx K) *ᵥ w = w ↔
      rotMat K (Multiplicative.toAdd v) *ᵥ (((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ w) =
        ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ w := by
  have hPP : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) * (F.P : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (F.P : Matrix Idx Idx K) * ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [c₀GL_coe, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun x => ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ x) h
    rwa [Matrix.mulVec_mulVec _ _ (F.P : Matrix Idx Idx K), hPP, Matrix.one_mulVec] at this
  · intro h
    rw [h, Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec]

theorem c₀_fixed_iff [Finite K] (F : Frame K) (v : F3Cube) (w : Idx → K) :
    (((c₀ F v : ↥(Omega7 K)) : GL Idx K) : Matrix Idx Idx K) *ᵥ w = w ↔
      ∀ i, Multiplicative.toAdd v i ≠ 0 →
        (((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ w) (.inl i) = 0 ∧
          (((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ w) (.inr (.inl i)) = 0 :=
  (c₀GL_mulVec_eq_self_iff F v w).trans (rotMat_mulVec_eq_self_iff F.h3 _ _)

theorem fix_iff [Finite K] (F : Frame K) (v : F3Cube) :
    {w : Idx → K | (((c₀ F v : ↥(Omega7 K)) : GL Idx K) : Matrix Idx Idx K) *ᵥ w = w} =
      {w : Idx → K | ∀ v' : F3Cube,
        (((c₀ F v' : ↥(Omega7 K)) : GL Idx K) : Matrix Idx Idx K) *ᵥ w = w} ↔
    ∀ i, Multiplicative.toAdd v i ≠ 0 := by
  have hPP : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) * (F.P : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  constructor
  · intro h i
    by_contra hi
    have hw : ((F.P : Matrix Idx Idx K) *ᵥ (Pi.single (.inl i) 1 : Idx → K)) ∈
        {w : Idx → K | ∀ v' : F3Cube,
          (((c₀ F v' : ↥(Omega7 K)) : GL Idx K) : Matrix Idx Idx K) *ᵥ w = w} := by
      rw [← h]
      show _ = _
      rw [c₀_fixed_iff, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
      intro j hj
      have hji : j ≠ i := fun e => hj (e ▸ hi)
      simp [Pi.single_apply, hji]
    have := hw (Multiplicative.ofAdd (Pi.single i 1))
    rw [c₀_fixed_iff, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec] at this
    have := (this i (by simp)).1
    simp at this
  · intro h
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hw v'
      rw [c₀_fixed_iff] at hw ⊢
      intro i _
      exact hw i (h i)
    · intro hw
      exact hw v

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
