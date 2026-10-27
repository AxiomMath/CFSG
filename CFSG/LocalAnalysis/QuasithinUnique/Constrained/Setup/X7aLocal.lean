module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGroup

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

section Local

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def frK (i : ℕ) : F →+* k := (iterateFrobenius k 2 i).comp (algebraMap F k)

theorem frK_apply (i : ℕ) (x : F) : frK k i x = algebraMap F k x ^ 2 ^ i := by
  simp [frK, iterateFrobenius_def]

@[expose] def twistMat (i : ℕ) (g : SL(3, F)) : Matrix (Fin 3) (Fin 3) k :=
  (frK k i).mapMatrix (g : Matrix (Fin 3) (Fin 3) F)

theorem twistMat_apply (i : ℕ) (g : SL(3, F)) (a b : Fin 3) :
    twistMat k i g a b = frK k i (g a b) := rfl

theorem twistMat_mul (i : ℕ) (g h : SL(3, F)) :
    twistMat k i (g * h) = twistMat k i g * twistMat k i h := by
  simp only [twistMat, Matrix.SpecialLinearGroup.coe_mul, map_mul]

theorem twistMat_one (i : ℕ) : twistMat k i (1 : SL(3, F)) = 1 := by
  simp [twistMat]

theorem twistMat_inv_mul (i : ℕ) (g : SL(3, F)) : twistMat k i g⁻¹ * twistMat k i g = 1 := by
  rw [← twistMat_mul, inv_mul_cancel, twistMat_one]

theorem twistMat_mul_inv (i : ℕ) (g : SL(3, F)) : twistMat k i g * twistMat k i g⁻¹ = 1 := by
  rw [← twistMat_mul, mul_inv_cancel, twistMat_one]

theorem twistMat_det (i : ℕ) (g : SL(3, F)) : (twistMat k i g).det = 1 := by
  rw [twistMat, ← RingHom.map_det, g.2, map_one]

@[expose] def natRep (i : ℕ) : SL(3, F) →* Matrix (Fin 3) (Fin 3) k where
  toFun := twistMat k i
  map_one' := twistMat_one k i
  map_mul' := twistMat_mul k i

@[expose] def dualRep (i : ℕ) : SL(3, F) →* Matrix (Fin 3) (Fin 3) k where
  toFun g := (twistMat k i g⁻¹)ᵀ
  map_one' := by simp [twistMat_one]
  map_mul' g h := by simp [mul_inv_rev, twistMat_mul, Matrix.transpose_mul]


section Coordinates

variable (k : Type*) [Field k]

@[expose] def Xm {k : Type*} [Add k] (c : Fin 8 → k) : Matrix (Fin 3) (Fin 3) k :=
  !![c 4, c 3, c 0; c 5, c 4 + c 2, c 1; c 7, c 6, c 2]

@[expose] def co {k : Type*} (X : Matrix (Fin 3) (Fin 3) k) : Fin 8 → k :=
  ![X 0 2, X 1 2, X 2 2, X 0 1, X 0 0, X 1 0, X 2 1, X 2 0]

theorem co_Xm {k : Type*} [Add k] (c : Fin 8 → k) : co (Xm c) = c := by
  funext r
  fin_cases r <;> simp [co, Xm]

@[expose] def XmL : (Fin 8 → k) →ₗ[k] Matrix (Fin 3) (Fin 3) k where
  toFun := Xm
  map_add' c d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm]
    all_goals ring
  map_smul' a c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm]
    all_goals ring

@[expose] def coL : Matrix (Fin 3) (Fin 3) k →ₗ[k] (Fin 8 → k) where
  toFun := co
  map_add' X Y := by
    funext r
    fin_cases r <;> simp [co]
  map_smul' a X := by
    funext r
    fin_cases r <;> simp [co]

theorem XmL_apply (c : Fin 8 → k) : XmL k c = Xm c := rfl

theorem coL_apply (X : Matrix (Fin 3) (Fin 3) k) : coL k X = co X := rfl

end Coordinates

section Adjoint

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

theorem two_eq_zero_k : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2

theorem trace_Xm (c : Fin 8 → k) : (Xm c).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag, Xm, Fin.sum_univ_three]
  simp
  linear_combination (c 4 + c 2) * two_eq_zero_k k

theorem Xm_co {X : Matrix (Fin 3) (Fin 3) k} (hX : X.trace = 0) : Xm (co X) = X := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [co, Xm]
  linear_combination hX - X 1 1 * two_eq_zero_k k

@[expose] def conjMat (i : ℕ) (g : SL(3, F)) (X : Matrix (Fin 3) (Fin 3) k) : Matrix (Fin 3) (Fin 3) k :=
  twistMat k i g * X * twistMat k i g⁻¹

theorem trace_conjMat (i : ℕ) (g : SL(3, F)) (X : Matrix (Fin 3) (Fin 3) k) :
    (conjMat k i g X).trace = X.trace := by
  rw [conjMat, Matrix.trace_mul_comm, ← mul_assoc, twistMat_inv_mul, one_mul]

theorem conjMat_mul (i : ℕ) (g h : SL(3, F)) (X : Matrix (Fin 3) (Fin 3) k) :
    conjMat k i (g * h) X = conjMat k i g (conjMat k i h X) := by
  simp only [conjMat, mul_inv_rev, twistMat_mul, mul_assoc]

theorem conjMat_one (i : ℕ) (X : Matrix (Fin 3) (Fin 3) k) :
    conjMat k i (1 : SL(3, F)) X = X := by
  simp [conjMat, twistMat_one]

@[expose] def conjLin (i : ℕ) (g : SL(3, F)) : Matrix (Fin 3) (Fin 3) k →ₗ[k] Matrix (Fin 3) (Fin 3) k :=
  LinearMap.mulLeft k (twistMat k i g) ∘ₗ LinearMap.mulRight k (twistMat k i g⁻¹)

theorem conjLin_apply (i : ℕ) (g : SL(3, F)) (X : Matrix (Fin 3) (Fin 3) k) :
    conjLin k i g X = conjMat k i g X := by
  simp [conjLin, conjMat, mul_assoc]

@[expose] def adjEnd (i : ℕ) : SL(3, F) →* Module.End k (Fin 8 → k) where
  toFun g := coL k ∘ₗ conjLin k i g ∘ₗ XmL k
  map_one' := by
    refine LinearMap.ext fun c => ?_
    simp [coL_apply, XmL_apply, conjLin_apply, conjMat_one, co_Xm]
  map_mul' g h := by
    refine LinearMap.ext fun c => ?_
    simp only [Module.End.mul_apply, LinearMap.comp_apply, coL_apply, XmL_apply, conjLin_apply]
    rw [Xm_co k (by rw [trace_conjMat, trace_Xm]), conjMat_mul]

theorem adjEnd_apply (i : ℕ) (g : SL(3, F)) (c : Fin 8 → k) :
    adjEnd k i g c = co (conjMat k i g (Xm c)) := by
  simp [adjEnd, coL_apply, XmL_apply, conjLin_apply]

@[expose] def adjRep (i : ℕ) : SL(3, F) →* Matrix (Fin 8) (Fin 8) k :=
  (LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin 8)).toMonoidHom.comp (adjEnd k i)

theorem adjRep_apply (i : ℕ) (g : SL(3, F)) (r s : Fin 8) :
    adjRep k i g r s = co (conjMat k i g (Xm (Pi.single s 1))) r := by
  simp [adjRep, LinearMap.toMatrixAlgEquiv', adjEnd_apply]

end Adjoint


section LocalFactors

@[expose] def locDim : Bool → Bool → ℕ
  | false, false => 1
  | true, false => 3
  | false, true => 3
  | true, true => 8

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def locRep (a b : Bool) (i : ℕ) :
    SL(3, F) →* Matrix (Fin (locDim a b)) (Fin (locDim a b)) k :=
  match a, b with
  | false, false => 1
  | true, false => natRep k i
  | false, true => dualRep k i
  | true, true => adjRep k i

@[expose] def locDist : (a b : Bool) → Fin (locDim a b)
  | false, false => ⟨0, by decide⟩
  | true, false => ⟨0, by decide⟩
  | false, true => ⟨2, by decide⟩
  | true, true => ⟨0, by decide⟩


@[expose] def locCoord : (a b : Bool) → Fin (locDim a b) → F → F → F → F
  | false, false => fun _ _ _ _ => 1
  | true, false => fun j x y _ => ![1, x, y] j
  | false, true => fun j x y z => ![y + x * z, z, 1] j
  | true, true => fun j x y z =>
      ![1, x, y, z, y + x * z, x * y + x ^ 2 * z, y * z, y ^ 2 + x * y * z] j

theorem twistMat_u3 (i : ℕ) (x y z : F) :
    twistMat k i (u3 x y z) = u3Mat (frK k i x) (frK k i y) (frK k i z) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [twistMat_apply, u3_coe, u3Mat]

theorem twistMat_up3 (i : ℕ) (x y z : F) :
    twistMat k i (up3 x y z) = upMat (frK k i x) (frK k i y) (frK k i z) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [twistMat_apply, up3_coe, upMat]

theorem adjRep_u3_col [CharP F 2] (i : ℕ) (x y z : F) (j : Fin 8) :
    adjRep k i (u3 x y z) j 0 =
      ![1, frK k i x, frK k i y, frK k i z, frK k i y + frK k i x * frK k i z,
        frK k i x * frK k i y + frK k i x ^ 2 * frK k i z, frK k i y * frK k i z,
        frK k i y ^ 2 + frK k i x * frK k i y * frK k i z] j := by
  rw [adjRep_apply, conjMat, u3_inv, twistMat_u3, twistMat_u3]
  have hX : Xm (Pi.single (0 : Fin 8) (1 : k)) = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Xm]
  rw [hX]
  fin_cases j <;> simp [co, u3Mat, Matrix.mul_apply, Fin.sum_univ_three, map_add, map_mul]
  all_goals ring


theorem natRep_apply (i : ℕ) (g : SL(3, F)) : natRep k i g = twistMat k i g := rfl

theorem dualRep_apply (i : ℕ) (g : SL(3, F)) : dualRep k i g = (twistMat k i g⁻¹)ᵀ := rfl

theorem locRep_ff (i : ℕ) : locRep (F := F) k false false i = 1 := rfl
theorem locRep_tf (i : ℕ) : locRep (F := F) k true false i = natRep k i := rfl
theorem locRep_ft (i : ℕ) : locRep (F := F) k false true i = dualRep k i := rfl
theorem locRep_tt (i : ℕ) : locRep (F := F) k true true i = adjRep k i := rfl

theorem fin_locDim_ff (j j' : Fin (locDim false false)) : j = j' :=
  Fin.ext (by have h1 := j.isLt; have h2 := j'.isLt; simp only [locDim] at h1 h2; omega)

theorem natRep_u3_col (i : ℕ) (x y z : F) (j : Fin 3) :
    natRep k i (u3 x y z) j 0 = frK k i (![1, x, y] j) := by
  rw [natRep_apply, twistMat_u3]
  fin_cases j <;> simp [u3Mat]

theorem dualRep_u3_col [CharP F 2] (i : ℕ) (x y z : F) (j : Fin 3) :
    dualRep k i (u3 x y z) j 2 = frK k i (![y + x * z, z, 1] j) := by
  rw [dualRep_apply, u3_inv, twistMat_u3]
  fin_cases j <;> simp [u3Mat, map_add, map_mul]

theorem adjRep_u3_col' [CharP F 2] (i : ℕ) (x y z : F) (j : Fin 8) :
    adjRep k i (u3 x y z) j 0 =
      frK k i (![1, x, y, z, y + x * z, x * y + x ^ 2 * z, y * z, y ^ 2 + x * y * z] j) := by
  rw [adjRep_u3_col]
  fin_cases j <;> simp [map_add, map_mul, map_pow]

theorem locRep_u3_col [CharP F 2] (a b : Bool) (i : ℕ) (x y z : F) (j : Fin (locDim a b)) :
    locRep k a b i (u3 x y z) j (locDist a b) = frK k i (locCoord a b j x y z) := by
  cases a <;> cases b
  · rw [locRep_ff, MonoidHom.one_apply, fin_locDim_ff j (locDist false false), Matrix.one_apply_eq]
    simp [locCoord]
  · exact dualRep_u3_col k i x y z j
  · exact natRep_u3_col k i x y z j
  · exact adjRep_u3_col' k i x y z j


@[expose] def locChar (a b : Bool) (r t : Fˣ) : F :=
  (if a then (r : F) else 1) * (if b then ((r * t : Fˣ) : F) else 1)

theorem dT_mul (r t r' t' : Fˣ) : (dT r t : SL(3, F)) * dT r' t' = dT (r * r') (t * t') :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, dT_coe, dT_coe, dT_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dTMat, Matrix.mul_apply, Fin.sum_univ_three, mul_inv_rev]
    all_goals ring)

theorem dT_one : (dT 1 1 : SL(3, F)) = 1 :=
  Subtype.ext (by
    rw [dT_coe, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dTMat])

theorem dT_inv (r t : Fˣ) : (dT r t : SL(3, F))⁻¹ = dT r⁻¹ t⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [dT_mul, mul_inv_cancel, mul_inv_cancel, dT_one]

theorem twistMat_dT (i : ℕ) (r t : Fˣ) :
    twistMat k i (dT r t) =
      !![frK k i (r : F), 0, 0; 0, frK k i (t : F), 0; 0, 0, frK k i (((r * t)⁻¹ : Fˣ) : F)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [twistMat_apply, dT_coe, dTMat]

theorem natRep_dT_col (i : ℕ) (r t : Fˣ) (j : Fin 3) :
    natRep k i (dT r t) j 0 = if j = 0 then frK k i (r : F) else 0 := by
  rw [natRep_apply, twistMat_dT]
  fin_cases j <;> simp

theorem dualRep_dT_col (i : ℕ) (r t : Fˣ) (j : Fin 3) :
    dualRep k i (dT r t) j 2 = if j = 2 then frK k i ((r * t : Fˣ) : F) else 0 := by
  have h : ((r⁻¹ * t⁻¹)⁻¹ : Fˣ) = r * t := by
    rw [mul_inv_rev, inv_inv, inv_inv, mul_comm]
  rw [dualRep_apply, dT_inv, twistMat_dT, h]
  fin_cases j <;> simp

theorem adjRep_dT_col (i : ℕ) (r t : Fˣ) (j : Fin 8) :
    adjRep k i (dT r t) j 0 = if j = 0 then frK k i ((r : F) * ((r * t : Fˣ) : F)) else 0 := by
  have h : ((r⁻¹ * t⁻¹)⁻¹ : Fˣ) = r * t := by
    rw [mul_inv_rev, inv_inv, inv_inv, mul_comm]
  have hX : Xm (Pi.single (0 : Fin 8) (1 : k)) = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Xm]
  rw [adjRep_apply, conjMat, dT_inv, twistMat_dT, twistMat_dT, hX, h]
  fin_cases j <;> simp [co, Matrix.mul_apply, Fin.sum_univ_three, map_mul]


theorem locChar_ff (r t : Fˣ) : locChar (F := F) false false r t = 1 := by simp [locChar]
theorem locChar_tf (r t : Fˣ) : locChar (F := F) true false r t = (r : F) := by simp [locChar]
theorem locChar_ft (r t : Fˣ) : locChar (F := F) false true r t = ((r * t : Fˣ) : F) := by
  simp [locChar]
theorem locChar_tt (r t : Fˣ) :
    locChar (F := F) true true r t = (r : F) * ((r * t : Fˣ) : F) := by simp [locChar]

theorem locRep_dT_col (a b : Bool) (i : ℕ) (r t : Fˣ) (j : Fin (locDim a b)) :
    locRep k a b i (dT r t) j (locDist a b) =
      if j = locDist a b then frK k i (locChar a b r t) else 0 := by
  cases a <;> cases b
  · rw [locRep_ff, MonoidHom.one_apply, fin_locDim_ff j (locDist false false), Matrix.one_apply_eq]
    simp [locChar]
  · rw [locChar_ft]
    exact dualRep_dT_col k i r t j
  · rw [locChar_tf]
    exact natRep_dT_col k i r t j
  · rw [locChar_tt]
    exact adjRep_dT_col k i r t j

theorem natRep_up3_col (i : ℕ) (x y z : F) (j : Fin 3) :
    natRep k i (up3 x y z) j 0 = if j = 0 then 1 else 0 := by
  rw [natRep_apply, twistMat_up3]
  fin_cases j <;> simp [upMat]

theorem dualRep_up3_col [CharP F 2] (i : ℕ) (x y z : F) (j : Fin 3) :
    dualRep k i (up3 x y z) j 2 = if j = 2 then 1 else 0 := by
  rw [dualRep_apply, up3_inv, twistMat_up3]
  fin_cases j <;> simp [upMat]

theorem adjRep_up3_col [CharP F 2] (i : ℕ) (x y z : F) (j : Fin 8) :
    adjRep k i (up3 x y z) j 0 = if j = 0 then 1 else 0 := by
  have hX : Xm (Pi.single (0 : Fin 8) (1 : k)) = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Xm]
  rw [adjRep_apply, conjMat, up3_inv, twistMat_up3, twistMat_up3, hX]
  fin_cases j <;> simp [co, upMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem locRep_up3_col [CharP F 2] (a b : Bool) (i : ℕ) (x y z : F) (j : Fin (locDim a b)) :
    locRep k a b i (up3 x y z) j (locDist a b) = if j = locDist a b then 1 else 0 := by
  cases a <;> cases b
  · rw [locRep_ff, MonoidHom.one_apply, fin_locDim_ff j (locDist false false), Matrix.one_apply_eq]
    simp
  · exact dualRep_up3_col k i x y z j
  · exact natRep_up3_col k i x y z j
  · exact adjRep_up3_col k i x y z j

end LocalFactors

end Local

end CFSG.QuasithinUnique.Setup.X7a
