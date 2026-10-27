module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.LU.Local.FiveStdInputs
public import CFSG.GH74.L5U5.ModelsBasic

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd.Mat

open CFSG.GH74.L5U5 Matrix

variable (F : Type) [Field F] [CharP F 5]

@[expose] def cF (i : Fin 5) : F := ZMod.castHom (dvd_refl 5) F (show ZMod 5 from i)

variable {F}

theorem cF_add (i j : Fin 5) : cF F (i + j) = cF F i + cF F j :=
  map_add (ZMod.castHom (dvd_refl 5) F) (show ZMod 5 from i) (show ZMod 5 from j)

theorem cF_mul (i j : Fin 5) : cF F (i * j) = cF F i * cF F j :=
  map_mul (ZMod.castHom (dvd_refl 5) F) (show ZMod 5 from i) (show ZMod 5 from j)

theorem cF_neg (i : Fin 5) : cF F (-i) = -cF F i :=
  map_neg (ZMod.castHom (dvd_refl 5) F) (show ZMod 5 from i)

theorem cF_sub (i j : Fin 5) : cF F (i - j) = cF F i - cF F j :=
  map_sub (ZMod.castHom (dvd_refl 5) F) (show ZMod 5 from i) (show ZMod 5 from j)

theorem cF_zero : cF F (0 : Fin 5) = 0 := map_zero (ZMod.castHom (dvd_refl 5) F)

theorem cF_one : cF F (1 : Fin 5) = 1 := map_one (ZMod.castHom (dvd_refl 5) F)

theorem cF_injective : Function.Injective (cF F) := fun i j h => by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact (ZMod.castHom (dvd_refl 5) F).injective (show (ZMod.castHom (dvd_refl 5) F) (show ZMod 5 from i) =
    (ZMod.castHom (dvd_refl 5) F) (show ZMod 5 from j) from h)

theorem cF_eq_zero {i : Fin 5} : cF F i = 0 ↔ i = 0 := by
  rw [← cF_zero (F := F)]
  exact cF_injective.eq_iff

theorem cF_surjective [Finite F] (hF : Nat.card F = 5) : Function.Surjective (cF F) :=
  (cF_injective.bijective_of_nat_card_le (by simp [hF])).2

theorem inv5_mul_self : ∀ d : Fin 5, d ≠ 0 → inv5 d * d = 1 := by decide

theorem pow4_eq_one : ∀ c : Fin 5, c ≠ 0 → c * c * c * c = 1 := by decide

@[expose] def mkM (a0 a1 a2 a3 : Fin 5) : Matrix (Fin 2) (Fin 2) F := !![cF F a0, cF F a1; cF F a2, cF F a3]

@[expose] def blkA (x : E) : Matrix (Fin 2) (Fin 2) F := mkM x.a0 x.a1 x.a2 x.a3

@[expose] def blkB (x : E) : Matrix (Fin 2) (Fin 2) F := mkM x.b0 x.b1 x.b2 x.b3

theorem mkM_mul (x0 x1 x2 x3 y0 y1 y2 y3 : Fin 5) :
    (mkM (x0 * y0 + x1 * y2) (x0 * y1 + x1 * y3) (x2 * y0 + x3 * y2) (x2 * y1 + x3 * y3) : Matrix (Fin 2) (Fin 2) F) =
      mkM x0 x1 x2 x3 * mkM y0 y1 y2 y3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkM, Matrix.mul_apply, Fin.sum_univ_two, cF_add, cF_mul]

theorem mkM_smul (c a0 a1 a2 a3 : Fin 5) :
    (mkM (c * a0) (c * a1) (c * a2) (c * a3) : Matrix (Fin 2) (Fin 2) F) = cF F c • mkM a0 a1 a2 a3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkM, cF_mul]

@[expose] def mat4 (x : E) : Matrix (Fin 4) (Fin 4) F :=
  blk4 (blkA x) (blkB x) * (if x.s then wMat else 1)

theorem det_blkA (x : E) : (blkA x : Matrix (Fin 2) (Fin 2) F).det = cF F (detA x) := by
  rw [blkA, mkM, Matrix.det_fin_two_of, detA, cF_sub, cF_mul, cF_mul]

theorem det_blkB (x : E) : (blkB x : Matrix (Fin 2) (Fin 2) F).det = cF F (detB x) := by
  rw [blkB, mkM, Matrix.det_fin_two_of, detB, cF_sub, cF_mul, cF_mul]

theorem det_mat4 (x : E) : (mat4 x : Matrix (Fin 4) (Fin 4) F).det = cF F (detA x * detB x) := by
  rw [mat4, Matrix.det_mul, det_blk4, det_blkA, det_blkB, cF_mul]
  split_ifs
  · rw [det_wMat, mul_one]
  · rw [Matrix.det_one, mul_one]

omit [CharP F 5] in
theorem blk4_smul (c : F) (A B : Matrix (Fin 2) (Fin 2) F) : blk4 (c • A) (c • B) = c • blk4 A B := by
  rw [blk4_eq_reindex, blk4_eq_reindex, ← map_smul, Matrix.fromBlocks_smul, smul_zero]

@[expose] def cn (z : E) : Fin 5 := inv5 (if z.a0 ≠ 0 then z.a0 else z.a1)

theorem blkA_normE (z : E) : (blkA (normE z) : Matrix (Fin 2) (Fin 2) F) = cF F (cn z) • blkA z :=
  mkM_smul (cn z) z.a0 z.a1 z.a2 z.a3

theorem blkB_normE (z : E) : (blkB (normE z) : Matrix (Fin 2) (Fin 2) F) = cF F (cn z) • blkB z :=
  mkM_smul (cn z) z.b0 z.b1 z.b2 z.b3

theorem mat4_normE (z : E) : (mat4 (normE z) : Matrix (Fin 4) (Fin 4) F) = cF F (cn z) • mat4 z := by
  rw [mat4, mat4, blkA_normE, blkB_normE, blk4_smul, Matrix.smul_mul]
  rfl

@[expose] def mulRaw (x y : E) : E :=
  match x.s, y.s with
  | false, false =>
    ⟨x.a0 * y.a0 + x.a1 * y.a2, x.a0 * y.a1 + x.a1 * y.a3, x.a2 * y.a0 + x.a3 * y.a2, x.a2 * y.a1 + x.a3 * y.a3,
      x.b0 * y.b0 + x.b1 * y.b2, x.b0 * y.b1 + x.b1 * y.b3, x.b2 * y.b0 + x.b3 * y.b2, x.b2 * y.b1 + x.b3 * y.b3, false⟩
  | false, true =>
    ⟨x.a0 * y.a0 + x.a1 * y.a2, x.a0 * y.a1 + x.a1 * y.a3, x.a2 * y.a0 + x.a3 * y.a2, x.a2 * y.a1 + x.a3 * y.a3,
      x.b0 * y.b0 + x.b1 * y.b2, x.b0 * y.b1 + x.b1 * y.b3, x.b2 * y.b0 + x.b3 * y.b2, x.b2 * y.b1 + x.b3 * y.b3, true⟩
  | true, false =>
    ⟨x.a0 * y.b0 + x.a1 * y.b2, x.a0 * y.b1 + x.a1 * y.b3, x.a2 * y.b0 + x.a3 * y.b2, x.a2 * y.b1 + x.a3 * y.b3,
      x.b0 * y.a0 + x.b1 * y.a2, x.b0 * y.a1 + x.b1 * y.a3, x.b2 * y.a0 + x.b3 * y.a2, x.b2 * y.a1 + x.b3 * y.a3, true⟩
  | true, true =>
    ⟨x.a0 * y.b0 + x.a1 * y.b2, x.a0 * y.b1 + x.a1 * y.b3, x.a2 * y.b0 + x.a3 * y.b2, x.a2 * y.b1 + x.a3 * y.b3,
      x.b0 * y.a0 + x.b1 * y.a2, x.b0 * y.a1 + x.b1 * y.a3, x.b2 * y.a0 + x.b3 * y.a2, x.b2 * y.a1 + x.b3 * y.a3, false⟩

theorem mulE_eq (x y : E) : mulE x y = normE (mulRaw x y) := by
  cases hx : x.s <;> cases hy : y.s <;> simp only [mulE, mulRaw, hx, hy]

omit [CharP F 5] in
theorem wMat_mul_blk4 (A B : Matrix (Fin 2) (Fin 2) F) :
    (wMat : Matrix (Fin 4) (Fin 4) F) * blk4 A B = blk4 B A * wMat := by
  have h := wMat_mul_blk4_mul_wMat A B
  calc (wMat : Matrix (Fin 4) (Fin 4) F) * blk4 A B = (wMat * blk4 A B * wMat) * wMat := by
        rw [Matrix.mul_assoc _ wMat wMat, wMat_mul_self, Matrix.mul_one]
    _ = blk4 B A * wMat := by rw [h]

theorem mat4_mulRaw (x y : E) : (mat4 (mulRaw x y) : Matrix (Fin 4) (Fin 4) F) = mat4 x * mat4 y := by
  cases hx : x.s <;> cases hy : y.s <;> simp [mat4, mulRaw, hx, hy, blkA, blkB]
  · rw [mkM_mul, mkM_mul, blk4_mul]
  · rw [mkM_mul, mkM_mul, ← Matrix.mul_assoc, blk4_mul]
  · rw [mkM_mul, mkM_mul, Matrix.mul_assoc _ wMat, wMat_mul_blk4, ← Matrix.mul_assoc, blk4_mul]
  · rw [mkM_mul, mkM_mul, Matrix.mul_assoc _ wMat, ← Matrix.mul_assoc wMat, wMat_mul_blk4,
      Matrix.mul_assoc _ wMat wMat, wMat_mul_self, Matrix.mul_one, blk4_mul]

theorem mat4_mulE (x y : E) :
    (mat4 (mulE x y) : Matrix (Fin 4) (Fin 4) F) = cF F (cn (mulRaw x y)) • (mat4 x * mat4 y) := by
  rw [mulE_eq, mat4_normE, mat4_mulRaw]

theorem det_mul2 : ∀ x0 x1 x2 x3 y0 y1 y2 y3 : ZMod 5,
    (x0 * y0 + x1 * y2) * (x2 * y1 + x3 * y3) - (x0 * y1 + x1 * y3) * (x2 * y0 + x3 * y2) =
      (x0 * x3 - x1 * x2) * (y0 * y3 - y1 * y2) := by
  intros
  ring

theorem det_smul2 : ∀ c a0 a1 a2 a3 b0 b1 b2 b3 : ZMod 5,
    ((c * a0) * (c * a3) - (c * a1) * (c * a2)) * ((c * b0) * (c * b3) - (c * b1) * (c * b2)) =
      (c * c * c * c) * ((a0 * a3 - a1 * a2) * (b0 * b3 - b1 * b2)) := by
  intros
  ring

theorem mul4_comm : ∀ p q r s : ZMod 5, p * q * (r * s) = (p * r) * (q * s) := by
  intros
  ring

theorem mul4_comm' : ∀ p q r s : ZMod 5, p * q * (r * s) = (p * r) * (s * q) := by
  intros
  ring

theorem validE_iff (x : E) : validE x = true ↔ isNorm x = true ∧ detA x * detB x = 1 := by
  simp [validE]

theorem mul_ne_zero_fin5 : ∀ a b : Fin 5, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide

theorem ne_zero_of_mul_eq_one : ∀ a b : Fin 5, a * b = 1 → a ≠ 0 ∧ b ≠ 0 := by decide

theorem inv5_ne_zero : ∀ d : Fin 5, d ≠ 0 → inv5 d ≠ 0 := by decide

theorem det_ne_zero_of_valid {x : E} (hx : validE x = true) : detA x ≠ 0 ∧ detB x ≠ 0 :=
  ne_zero_of_mul_eq_one _ _ ((validE_iff x).1 hx).2

theorem cn_ne_zero {z : E} (hA : detA z ≠ 0) : cn z ≠ 0 := by
  unfold cn
  apply inv5_ne_zero
  by_cases h0 : z.a0 = 0
  · simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte]
    intro h1
    apply hA
    simp [detA, h0, h1]
  · simp [h0]

theorem isNorm_normE {z : E} (hA : detA z ≠ 0) : isNorm (normE z) = true := by
  by_cases h0 : z.a0 = 0
  · have h1 : z.a1 ≠ 0 := fun h1 => hA (by simp [detA, h0, h1])
    simp only [isNorm, normE, h0, ne_eq, not_true_eq_false, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    right
    refine ⟨by simp, ?_⟩
    exact inv5_mul_self _ h1
  · simp only [isNorm, normE, h0, ne_eq, not_false_eq_true, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq]
    left
    exact inv5_mul_self _ h0

theorem detprod_normE {z : E} (hA : detA z ≠ 0) :
    detA (normE z) * detB (normE z) = detA z * detB z := by
  have hc := pow4_eq_one _ (cn_ne_zero hA)
  have : detA (normE z) * detB (normE z) = (cn z * cn z * cn z * cn z) * (detA z * detB z) :=
    det_smul2 (cn z) z.a0 z.a1 z.a2 z.a3 z.b0 z.b1 z.b2 z.b3
  rw [this, hc, one_mul]

theorem validE_normE {z : E} (hA : detA z ≠ 0) (hP : detA z * detB z = 1) : validE (normE z) = true :=
  (validE_iff _).2 ⟨isNorm_normE hA, by rw [detprod_normE hA, hP]⟩

theorem detA_mulRaw_of_false {x : E} (y : E) (hx : x.s = false) : detA (mulRaw x y) = detA x * detA y := by
  cases hy : y.s <;> simp only [mulRaw, hx, hy, detA] <;> exact det_mul2 x.a0 x.a1 x.a2 x.a3 y.a0 y.a1 y.a2 y.a3

theorem detB_mulRaw_of_false {x : E} (y : E) (hx : x.s = false) : detB (mulRaw x y) = detB x * detB y := by
  cases hy : y.s <;> simp only [mulRaw, hx, hy, detB] <;> exact det_mul2 x.b0 x.b1 x.b2 x.b3 y.b0 y.b1 y.b2 y.b3

theorem detA_mulRaw_of_true {x : E} (y : E) (hx : x.s = true) : detA (mulRaw x y) = detA x * detB y := by
  cases hy : y.s <;> simp only [mulRaw, hx, hy, detA, detB] <;> exact det_mul2 x.a0 x.a1 x.a2 x.a3 y.b0 y.b1 y.b2 y.b3

theorem detB_mulRaw_of_true {x : E} (y : E) (hx : x.s = true) : detB (mulRaw x y) = detB x * detA y := by
  cases hy : y.s <;> simp only [mulRaw, hx, hy, detA, detB] <;> exact det_mul2 x.b0 x.b1 x.b2 x.b3 y.a0 y.a1 y.a2 y.a3

theorem validE_mulE {x y : E} (hx : validE x = true) (hy : validE y = true) :
    validE (mulE x y) = true := by
  obtain ⟨hxA, hxB⟩ := det_ne_zero_of_valid hx
  obtain ⟨hyA, hyB⟩ := det_ne_zero_of_valid hy
  have hx1 := ((validE_iff x).1 hx).2
  have hy1 := ((validE_iff y).1 hy).2
  rw [mulE_eq]
  cases hs : x.s
  · refine validE_normE (by rw [detA_mulRaw_of_false y hs]; exact mul_ne_zero_fin5 _ _ hxA hyA) ?_
    rw [detA_mulRaw_of_false y hs, detB_mulRaw_of_false y hs]
    calc detA x * detA y * (detB x * detB y) = (detA x * detB x) * (detA y * detB y) :=
        mul4_comm _ _ _ _
      _ = 1 := by rw [hx1, hy1, one_mul]
  · refine validE_normE (by rw [detA_mulRaw_of_true y hs]; exact mul_ne_zero_fin5 _ _ hxA hyB) ?_
    rw [detA_mulRaw_of_true y hs, detB_mulRaw_of_true y hs]
    calc detA x * detB y * (detB x * detA y) = (detA x * detB x) * (detA y * detB y) :=
        mul4_comm' _ _ _ _
      _ = 1 := by rw [hx1, hy1, one_mul]

end CFSG.GH74.GLS.LU.Local.FiveStd.Mat
