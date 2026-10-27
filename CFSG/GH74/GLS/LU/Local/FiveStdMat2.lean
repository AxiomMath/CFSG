module

public import CFSG.GH74.GLS.LU.Local.FiveStdMat1

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd.Mat

open CFSG.GH74.L5U5 Matrix

variable {F : Type} [Field F] [CharP F 5]

@[expose] def invRaw (x : E) : E :=
  let ia := invA x
  let ib := invB x
  match x.s with
  | false => ⟨ia.1, ia.2.1, ia.2.2.1, ia.2.2.2, ib.1, ib.2.1, ib.2.2.1, ib.2.2.2, false⟩
  | true => ⟨ib.1, ib.2.1, ib.2.2.1, ib.2.2.2, ia.1, ia.2.1, ia.2.2.1, ia.2.2.2, true⟩

theorem invE_eq (x : E) : invE x = normE (invRaw x) := by
  unfold invE invRaw
  cases x.s <;> rfl

theorem mat_inv_aux : ∀ a0 a1 a2 a3 d : ZMod 5,
    (a0 * (d * a3) + a1 * (-(d * a2)) = d * (a0 * a3 - a1 * a2)) ∧
    (a0 * (-(d * a1)) + a1 * (d * a0) = 0) ∧
    (a2 * (d * a3) + a3 * (-(d * a2)) = 0) ∧
    (a2 * (-(d * a1)) + a3 * (d * a0) = d * (a0 * a3 - a1 * a2)) := by
  intros
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem mkM_inv (a0 a1 a2 a3 : Fin 5) (h : inv5 (a0 * a3 - a1 * a2) * (a0 * a3 - a1 * a2) = 1) :
    (mkM a0 a1 a2 a3 : Matrix (Fin 2) (Fin 2) F) *
      mkM (inv5 (a0 * a3 - a1 * a2) * a3) (-(inv5 (a0 * a3 - a1 * a2) * a1))
        (-(inv5 (a0 * a3 - a1 * a2) * a2)) (inv5 (a0 * a3 - a1 * a2) * a0) = 1 := by
  rw [← mkM_mul]
  obtain ⟨h1, h2, h3, h4⟩ := mat_inv_aux a0 a1 a2 a3 (inv5 (a0 * a3 - a1 * a2))
  have e1 : a0 * (inv5 (a0 * a3 - a1 * a2) * a3) + a1 * (-(inv5 (a0 * a3 - a1 * a2) * a2)) = 1 :=
    h1.trans h
  have e2 : a0 * (-(inv5 (a0 * a3 - a1 * a2) * a1)) + a1 * (inv5 (a0 * a3 - a1 * a2) * a0) = 0 := h2
  have e3 : a2 * (inv5 (a0 * a3 - a1 * a2) * a3) + a3 * (-(inv5 (a0 * a3 - a1 * a2) * a2)) = 0 := h3
  have e4 : a2 * (-(inv5 (a0 * a3 - a1 * a2) * a1)) + a3 * (inv5 (a0 * a3 - a1 * a2) * a0) = 1 :=
    h4.trans h
  rw [e1, e2, e3, e4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkM, cF_zero, cF_one]

theorem dA_mul_detA {x : E} (hx : validE x = true) : inv5 (detA x) * detA x = 1 :=
  inv5_mul_self _ (det_ne_zero_of_valid hx).1

theorem dB_mul_detB {x : E} (hx : validE x = true) : inv5 (detB x) * detB x = 1 :=
  inv5_mul_self _ (det_ne_zero_of_valid hx).2

theorem mat4_invRaw {x : E} (hx : validE x = true) :
    (mat4 x : Matrix (Fin 4) (Fin 4) F) * mat4 (invRaw x) = 1 := by
  have hA := mkM_inv (F := F) x.a0 x.a1 x.a2 x.a3 (dA_mul_detA hx)
  have hB := mkM_inv (F := F) x.b0 x.b1 x.b2 x.b3 (dB_mul_detB hx)
  cases hs : x.s
  · simp only [mat4, invRaw, hs, blkA, blkB, invA, invB, detA, detB] at hA hB ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one]
    rw [blk4_mul, hA, hB, blk4_one]
  · simp only [mat4, invRaw, hs, blkA, blkB, invA, invB, detA, detB] at hA hB ⊢
    simp only [↓reduceIte]
    rw [Matrix.mul_assoc _ wMat, ← Matrix.mul_assoc wMat, wMat_mul_blk4_mul_wMat, blk4_mul, hA, hB, blk4_one]

theorem inv_aux1 : ∀ d t : Fin 5, d * t = 1 → d * (d * t) = d := by decide

theorem inv_aux2 : ∀ p q a b : Fin 5, p * a = 1 → q * b = 1 → a * b = 1 → p * q = 1 := by decide

theorem inv_aux2' : ∀ p q a b : Fin 5, p * a = 1 → q * b = 1 → a * b = 1 → q * p = 1 := by decide

theorem inv_det (a0 a1 a2 a3 d : Fin 5) (h : d * (a0 * a3 - a1 * a2) = 1) :
    (d * a3) * (d * a0) - (-(d * a1)) * (-(d * a2)) = d := by
  have key : ∀ a0 a1 a2 a3 d : ZMod 5,
      (d * a3) * (d * a0) - (-(d * a1)) * (-(d * a2)) = d * (d * (a0 * a3 - a1 * a2)) := by
    intros
    ring
  exact (key a0 a1 a2 a3 d).trans (inv_aux1 _ _ h)

theorem detA_invRaw_false {x : E} (hx : validE x = true) (hs : x.s = false) :
    detA (invRaw x) = inv5 (detA x) := by
  simp only [invRaw, hs, detA, invA]
  exact inv_det x.a0 x.a1 x.a2 x.a3 _ (dA_mul_detA hx)

theorem detB_invRaw_false {x : E} (hx : validE x = true) (hs : x.s = false) :
    detB (invRaw x) = inv5 (detB x) := by
  simp only [invRaw, hs, detB, invB]
  exact inv_det x.b0 x.b1 x.b2 x.b3 _ (dB_mul_detB hx)

theorem detA_invRaw_true {x : E} (hx : validE x = true) (hs : x.s = true) :
    detA (invRaw x) = inv5 (detB x) := by
  simp only [invRaw, hs, detA, invB]
  exact inv_det x.b0 x.b1 x.b2 x.b3 _ (dB_mul_detB hx)

theorem detB_invRaw_true {x : E} (hx : validE x = true) (hs : x.s = true) :
    detB (invRaw x) = inv5 (detA x) := by
  simp only [invRaw, hs, detB, invA]
  exact inv_det x.a0 x.a1 x.a2 x.a3 _ (dA_mul_detA hx)

theorem validE_invE {x : E} (hx : validE x = true) : validE (invE x) = true := by
  rw [invE_eq]
  obtain ⟨hA, hB⟩ := det_ne_zero_of_valid hx
  have h1 := dA_mul_detA hx
  have h2 := dB_mul_detB hx
  have h3 := ((validE_iff x).1 hx).2
  cases hs : x.s
  · refine validE_normE ?_ ?_
    · rw [detA_invRaw_false hx hs]
      exact inv5_ne_zero _ hA
    · rw [detA_invRaw_false hx hs, detB_invRaw_false hx hs]
      exact inv_aux2 _ _ _ _ h1 h2 h3
  · refine validE_normE ?_ ?_
    · rw [detA_invRaw_true hx hs]
      exact inv5_ne_zero _ hB
    · rw [detA_invRaw_true hx hs, detB_invRaw_true hx hs]
      exact inv_aux2' _ _ _ _ h1 h2 h3

theorem mat4_mul_invE {x : E} (hx : validE x = true) :
    (mat4 x : Matrix (Fin 4) (Fin 4) F) * mat4 (invE x) = cF F (cn (invRaw x)) • 1 := by
  rw [invE_eq, mat4_normE, Matrix.mul_smul, mat4_invRaw hx]

end CFSG.GH74.GLS.LU.Local.FiveStd.Mat
