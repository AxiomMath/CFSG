module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpARadicalComm
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix

variable {K : Type} [Field K] {N j : ℕ}

section Form

variable (hjN : 2 * j = N)
include hjN

theorem spAPar_spAPar_lag (k : Fin N) : spAPar (spAPar k) = k :=
  spAPar_spAPar hjN.le (by have := k.isLt; omega)

theorem spAPar_ne_lag (k : Fin N) : spAPar k ≠ k :=
  spAPar_ne hjN.le (by have := k.isLt; omega)

theorem spAPar_eq_iff_lag {k l : Fin N} : spAPar k = l ↔ k = spAPar l := by
  constructor
  · rintro rfl
    rw [spAPar_spAPar_lag hjN]
  · rintro rfl
    rw [spAPar_spAPar_lag hjN]

theorem spARepMat_apply_lag (m l : Fin N) :
    (spARepMat N j : Matrix (Fin N) (Fin N) K) m l = if m = spAPar l then 1 else 0 := by
  rw [spARepMat_apply hjN.le]
  congr 1
  exact propext ⟨fun h => h.2, fun h => ⟨by have := l.isLt; omega, h⟩⟩

theorem spARepMat_mulVec_lag (v : Fin N → K) :
    (spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ v = fun k => v (spAPar k) := by
  ext k
  rw [Matrix.mulVec, dotProduct, sum_spARepMat_mul hjN.le v k,
    ite_eq_left (by have := k.isLt; omega)]

theorem spARepMat_mulVec_single_lag (a : Fin N) :
    (spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ Pi.single a 1 = Pi.single (spAPar a) 1 := by
  rw [spARepMat_mulVec_lag hjN]
  ext k
  simp only [Pi.single_apply, spAPar_eq_iff_lag hjN]

theorem spARepMat_mulVec_mulVec_lag (v : Fin N → K) :
    (spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ
      ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ v) = v := by
  rw [spARepMat_mulVec_lag hjN, spARepMat_mulVec_lag hjN]
  ext k
  simp only [spAPar_spAPar_lag hjN]

theorem spARepMat_mulVec_dotProduct_self_lag [CharP K 2] (v : Fin N → K) :
    ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ v) ⬝ᵥ v = 0 := by
  rw [spARepMat_mulVec_lag hjN, dotProduct]
  refine Finset.sum_ninvolution spAPar (fun k => ?_) (fun k _ => spAPar_ne_lag hjN k)
    (fun _ => Finset.mem_univ _) (spAPar_spAPar_lag hjN)
  rw [spAPar_spAPar_lag hjN, mul_comm (v k)]
  exact CharTwo.add_self_eq_zero _

end Form

section Unit

variable [CharP K 2]

theorem lagMat_add_self (A : Matrix (Fin N) (Fin N) K) : A + A = 0 := by
  ext a b
  rw [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem lagVec_add_self (v : Fin N → K) : v + v = 0 := by
  ext a
  rw [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem lagSqZero_mul_self {x y : Fin N → K} (h : y ⬝ᵥ x = 0) :
    (1 + vecMulVec x y) * (1 + vecMulVec x y) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero, add_zero, add_assoc,
    lagMat_add_self, add_zero]

@[expose] def lagSqZeroUnit (x y : Fin N → K) (h : y ⬝ᵥ x = 0) : GL (Fin N) K where
  val := 1 + vecMulVec x y
  inv := 1 + vecMulVec x y
  val_inv := lagSqZero_mul_self h
  inv_val := lagSqZero_mul_self h

theorem coe_lagSqZeroUnit {x y : Fin N → K} (h : y ⬝ᵥ x = 0) :
    ((lagSqZeroUnit x y h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1 + vecMulVec x y := rfl

theorem lagSqZeroUnit_inv {x y : Fin N → K} (h : y ⬝ᵥ x = 0) :
    (lagSqZeroUnit x y h)⁻¹ = lagSqZeroUnit x y h :=
  inv_eq_of_mul_eq_one_right (Units.ext (lagSqZero_mul_self h))

omit [CharP K 2] in
theorem lagSqZero_mulVec (x y v : Fin N → K) :
    (1 + vecMulVec x y) *ᵥ v = v + (y ⬝ᵥ v) • x := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

omit [CharP K 2] in
theorem mul_vecMulVec_mul_transpose_lag (M : Matrix (Fin N) (Fin N) K) (x y : Fin N → K) :
    M * vecMulVec x y * Mᵀ = vecMulVec (M *ᵥ x) (M *ᵥ y) := by
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

omit [CharP K 2] in
theorem lagSqZero_conj (x y : Fin N → K) {Y : Matrix (Fin N) (Fin N) K} (hY : Yᵀ = Y) :
    (1 + vecMulVec x y) * Y * (1 + vecMulVec x y)ᵀ =
      Y + (vecMulVec x (Y *ᵥ y) + vecMulVec (Y *ᵥ y) x +
        ((Y *ᵥ y) ⬝ᵥ y) • vecMulVec x x) := by
  have h1 : y ᵥ* Y = Y *ᵥ y := by
    conv_lhs => rw [← hY]
    exact vecMul_transpose Y y
  rw [transpose_add, transpose_one, transpose_vecMulVec, Matrix.add_mul, Matrix.one_mul,
    vecMulVec_mul, h1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, mul_vecMulVec,
    Matrix.mul_add, Matrix.mul_one, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  abel

variable (hjN : 2 * j = N)

variable (j) in
@[expose] def lagTvMat (w : Fin N → K) : Matrix (Fin N) (Fin N) K :=
  1 + vecMulVec w ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ w)

@[expose] def lagTvUnit (w : Fin N → K) : GL (Fin N) K :=
  lagSqZeroUnit w ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ w)
    (spARepMat_mulVec_dotProduct_self_lag hjN w)

theorem coe_lagTvUnit (w : Fin N → K) :
    ((lagTvUnit hjN w : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = lagTvMat j w := rfl

include hjN in
theorem lagTv_conj_spARepMat (w : Fin N → K) :
    lagTvMat j w * (spARepMat N j : Matrix (Fin N) (Fin N) K) * (lagTvMat j w)ᵀ =
      spARepMat N j := by
  rw [lagTvMat, lagSqZero_conj _ _ (spARepMat_transpose N j), spARepMat_mulVec_mulVec_lag hjN,
    dotProduct_comm, spARepMat_mulVec_dotProduct_self_lag hjN, zero_smul, add_zero,
    lagMat_add_self, add_zero]

omit [CharP K 2] in
include hjN in
theorem lagTvMat_mulVec_single (w : Fin N → K) (i : Fin N) :
    lagTvMat j w *ᵥ Pi.single i 1 = Pi.single i 1 + w (spAPar i) • w := by
  rw [lagTvMat, lagSqZero_mulVec, dotProduct_single_one, spARepMat_mulVec_lag hjN]

end Unit

section Fix

variable [CharP K 2]

omit [CharP K 2] in
theorem lagTv_fix_entry {w : Fin N → K} {Y : Matrix (Fin N) (Fin N) K} (hY : Yᵀ = Y)
    (h : lagTvMat j w * Y * (lagTvMat j w)ᵀ = Y) (a b : Fin N) :
    w a * (Y *ᵥ ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ w)) b +
      (Y *ᵥ ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ w)) a * w b +
      ((Y *ᵥ ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ w)) ⬝ᵥ
        ((spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ w)) * (w a * w b) = 0 := by
  rw [lagTvMat, lagSqZero_conj _ _ hY, add_eq_left] at h
  have h2 := congrFun (congrFun h a) b
  simpa only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Matrix.zero_apply] using h2

variable (hjN : 2 * j = N)
include hjN

theorem eq_of_forall_lagTv_fix (i0 : Fin N) {Y : Matrix (Fin N) (Fin N) K} (hY : Yᵀ = Y)
    (hfix : ∀ w : Fin N → K, w (spAPar i0) = 0 → lagTvMat j w * Y * (lagTvMat j w)ᵀ = Y) :
    Y = Y i0 i0 • vecMulVec (Pi.single i0 1) (Pi.single i0 1) +
      Y i0 (spAPar i0) • (spARepMat N j : Matrix (Fin N) (Fin N) K) := by
  have hi01 : i0 ≠ spAPar i0 := (spAPar_ne_lag hjN i0).symm
  have hpp : ∀ k, spAPar (spAPar k) = k := spAPar_spAPar_lag hjN
  have hYs : ∀ a b, Y a b = Y b a := fun a b => by
    rw [← transpose_apply Y b a, hY]
  have Z1 : ∀ a, a ≠ spAPar i0 → ∀ b, b ≠ a → Y b (spAPar a) = 0 := by
    intro a ha b hb
    have hw : (Pi.single a (1 : K) : Fin N → K) (spAPar i0) = 0 :=
      Pi.single_eq_of_ne (Ne.symm ha) 1
    have e := lagTv_fix_entry hY (hfix _ hw) a b
    rw [spARepMat_mulVec_single_lag hjN, mulVec_single_one] at e
    simpa [Pi.single_apply, hb] using e
  have Z2 : ∀ a, a ≠ spAPar i0 → Y (spAPar a) (spAPar a) = 0 := by
    intro a ha
    have hw : (Pi.single a (1 : K) : Fin N → K) (spAPar i0) = 0 :=
      Pi.single_eq_of_ne (Ne.symm ha) 1
    have e := lagTv_fix_entry hY (hfix _ hw) a a
    rw [spARepMat_mulVec_single_lag hjN, mulVec_single_one, dotProduct_single_one] at e
    simp only [Pi.single_eq_same, one_mul, mul_one, Matrix.col_apply] at e
    rwa [CharTwo.add_self_eq_zero, zero_add] at e
  have Z3 : ∀ c, c ≠ i0 → c ≠ spAPar i0 → Y c (spAPar c) = Y i0 (spAPar i0) := by
    intro c hc0 hc1
    set w : Fin N → K := Pi.single i0 1 + Pi.single c 1 with hwdef
    have hw : w (spAPar i0) = 0 := by
      rw [hwdef, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hi01), Pi.single_eq_of_ne (Ne.symm hc1),
        add_zero]
    have e := lagTv_fix_entry hY (hfix _ hw) i0 c
    have hSw : (spARepMat N j : Matrix (Fin N) (Fin N) K) *ᵥ w =
        Pi.single (spAPar i0) 1 + Pi.single (spAPar c) 1 := by
      rw [hwdef, Matrix.mulVec_add, spARepMat_mulVec_single_lag hjN,
        spARepMat_mulVec_single_lag hjN]
    have hw0 : w i0 = 1 := by
      rw [hwdef, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hc0), add_zero]
    have hwc : w c = 1 := by
      rw [hwdef, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hc0, zero_add]
    rw [hSw, hw0, hwc, Matrix.mulVec_add, mulVec_single_one, mulVec_single_one, dotProduct_add,
      dotProduct_single_one, dotProduct_single_one] at e
    simp only [Pi.add_apply, Matrix.col_apply, one_mul, mul_one] at e
    have h1 : Y c (spAPar i0) = 0 := Z1 i0 hi01 c hc0
    have h2 : Y i0 (spAPar c) = 0 := Z1 c hc1 i0 (Ne.symm hc0)
    have h3 : Y (spAPar i0) (spAPar i0) = 0 := Z2 i0 hi01
    have h4 : Y (spAPar c) (spAPar c) = 0 := Z2 c hc1
    rw [h1, h2, h3, h4, hYs (spAPar c) (spAPar i0)] at e
    linear_combination e - (Y i0 (spAPar i0) + Y (spAPar i0) (spAPar c)) *
      (CharTwo.two_eq_zero (R := K))
  ext r t
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, vecMulVec_apply,
    spARepMat_apply_lag hjN, smul_eq_mul, smul_eq_mul]
  by_cases ht : t = i0
  · rw [ht]
    by_cases hr : r = i0
    · rw [hr, ite_eq_right hi01, Pi.single_eq_same, mul_one, mul_one, mul_zero, add_zero]
    · rw [Pi.single_eq_of_ne hr, zero_mul, mul_zero, zero_add]
      by_cases hr1 : r = spAPar i0
      · rw [ite_eq_left hr1, mul_one, hr1]
        exact hYs _ _
      · rw [ite_eq_right hr1, mul_zero, hYs]
        have h := Z1 (spAPar r) (fun h => hr (by rw [← hpp r, h, hpp]))
          i0 (fun h => hr1 (by rw [h, hpp]))
        rwa [hpp] at h
  · rw [Pi.single_eq_of_ne ht, mul_zero, mul_zero, zero_add]
    have ha : spAPar t ≠ spAPar i0 := fun h => ht (by rw [← hpp t, h, hpp])
    by_cases hr : r = spAPar t
    · rw [ite_eq_left hr, mul_one, hr]
      by_cases hc0 : spAPar t = i0
      · have e1 : t = spAPar i0 := by rw [← hc0, hpp]
        rw [hc0, e1]
      · have h := Z3 (spAPar t) hc0 ha
        rwa [hpp] at h
    · rw [ite_eq_right hr, mul_zero]
      have h := Z1 (spAPar t) ha r hr
      rwa [hpp] at h

omit hjN in
theorem vecMulVec_add_vecMulVec_eq_sum (e x y : Fin N → K) :
    vecMulVec x y + vecMulVec y x = vecMulVec e e + vecMulVec (e + x) (e + x) +
      vecMulVec (e + y) (e + y) + vecMulVec (e + x + y) (e + x + y) := by
  ext r t
  simp only [Matrix.add_apply, vecMulVec_apply, Pi.add_apply]
  linear_combination (-(2 * e r * e t + e r * x t + x r * e t + x r * x t + e r * y t +
    y r * e t + y r * y t)) * (CharTwo.two_eq_zero (R := K))

theorem lagModule_eq (hK : Nat.card K = 2) (i0 : Fin N)
    (F : Matrix (Fin N) (Fin N) K → Matrix (Fin N) (Fin N) K)
    (hsym : ∀ X, Xᵀ = X → (F X)ᵀ = F X)
    (hadd : ∀ X Y, Xᵀ = X → Yᵀ = Y → F (X + Y) = F X + F Y)
    (hzero : ∀ X, Xᵀ = X → F X = 0 → X = 0)
    (hS : F (spARepMat N j) = spARepMat N j)
    (hT : ∀ (w : Fin N → K) (X : Matrix (Fin N) (Fin N) K), Xᵀ = X →
      F (lagTvMat j w * X * (lagTvMat j w)ᵀ) = lagTvMat j w * F X * (lagTvMat j w)ᵀ)
    {x y : Fin N → K} (hx : x (spAPar i0) = 0) (hy : y (spAPar i0) = 0) :
    F (vecMulVec x y + vecMulVec y x) = vecMulVec x y + vecMulVec y x := by
  have hi01 : i0 ≠ spAPar i0 := (spAPar_ne_lag hjN i0).symm
  have hP : ∀ v : Fin N → K, (vecMulVec v v)ᵀ = vecMulVec v v := fun v => transpose_vecMulVec v v
  have hSt : (spARepMat N j : Matrix (Fin N) (Fin N) K)ᵀ = spARepMat N j :=
    spARepMat_transpose N j
  have hTe0 : ∀ w : Fin N → K,
      lagTvMat j w *ᵥ Pi.single i0 1 = Pi.single i0 1 + w (spAPar i0) • w :=
    fun w => lagTvMat_mulVec_single hjN w i0
  have hY : (F (vecMulVec (Pi.single i0 1) (Pi.single i0 1)))ᵀ =
      F (vecMulVec (Pi.single i0 1) (Pi.single i0 1)) := hsym _ (hP _)
  have hfix : ∀ w : Fin N → K, w (spAPar i0) = 0 →
      lagTvMat j w * F (vecMulVec (Pi.single i0 1) (Pi.single i0 1)) * (lagTvMat j w)ᵀ =
        F (vecMulVec (Pi.single i0 1) (Pi.single i0 1)) := by
    intro w hw
    have h := hT w (vecMulVec (Pi.single i0 1) (Pi.single i0 1)) (hP _)
    rw [mul_vecMulVec_mul_transpose_lag, hTe0, hw, zero_smul, add_zero] at h
    exact h.symm
  have hY' := eq_of_forall_lagTv_fix hjN i0 hY hfix
  set Y := F (vecMulVec (Pi.single i0 1) (Pi.single i0 1)) with hYdef
  have hS0 : (spARepMat N j : Matrix (Fin N) (Fin N) K) i0 i0 = 0 := by
    rw [spARepMat_apply_lag hjN, ite_eq_right hi01]
  have hE0 : vecMulVec (Pi.single i0 (1 : K)) (Pi.single i0 1) i0 i0 = 1 := by
    rw [vecMulVec_apply, Pi.single_eq_same, mul_one]
  have hY00 : Y i0 i0 = 1 := by
    rcases eq_zero_or_eq_one_of_natCard_two hK (Y i0 i0) with h0 | h1
    · exfalso
      rw [h0, zero_smul, zero_add] at hY'
      rcases eq_zero_or_eq_one_of_natCard_two hK (Y i0 (spAPar i0)) with h0' | h1'
      · rw [h0', zero_smul] at hY'
        have := congrFun (congrFun (hzero _ (hP _) hY') i0) i0
        rw [hE0, Matrix.zero_apply] at this
        exact one_ne_zero this
      · rw [h1', one_smul] at hY'
        have h2 : F (vecMulVec (Pi.single i0 1) (Pi.single i0 1) + spARepMat N j) = 0 := by
          rw [hadd _ _ (hP _) hSt, ← hYdef, hY', hS, lagMat_add_self]
        have := congrFun (congrFun (hzero _ (by rw [transpose_add, hP, hSt]) h2) i0) i0
        rw [Matrix.add_apply, hE0, hS0, add_zero, Matrix.zero_apply] at this
        exact one_ne_zero this
    · exact h1
  have hF0 : Y = vecMulVec (Pi.single i0 1) (Pi.single i0 1) +
      Y i0 (spAPar i0) • (spARepMat N j : Matrix (Fin N) (Fin N) K) := by
    conv_lhs => rw [hY']
    rw [hY00, one_smul]
  have hFv : ∀ v : Fin N → K, v (spAPar i0) = 1 → F (vecMulVec v v) =
      vecMulVec v v + Y i0 (spAPar i0) • (spARepMat N j : Matrix (Fin N) (Fin N) K) := by
    intro v hv
    have hw : (v + Pi.single i0 1 : Fin N → K) (spAPar i0) = 1 := by
      rw [Pi.add_apply, hv, Pi.single_eq_of_ne (Ne.symm hi01), add_zero]
    have hTv : lagTvMat j (v + Pi.single i0 1) *ᵥ Pi.single i0 1 = v := by
      rw [hTe0, hw, one_smul, add_comm v, ← add_assoc, lagVec_add_self, zero_add]
    have h := hT (v + Pi.single i0 1) (vecMulVec (Pi.single i0 1) (Pi.single i0 1)) (hP _)
    rw [mul_vecMulVec_mul_transpose_lag, hTv, ← hYdef, hF0, Matrix.mul_add, Matrix.add_mul,
      mul_vecMulVec_mul_transpose_lag, hTv, Matrix.mul_smul, Matrix.smul_mul,
      lagTv_conj_spARepMat hjN] at h
    exact h
  have h1 : (Pi.single (spAPar i0) (1 : K) : Fin N → K) (spAPar i0) = 1 := Pi.single_eq_same _ _
  have hsum : ∀ A B : Matrix (Fin N) (Fin N) K, Aᵀ = A → Bᵀ = B → (A + B)ᵀ = A + B :=
    fun A B hA hB => by rw [transpose_add, hA, hB]
  rw [vecMulVec_add_vecMulVec_eq_sum (Pi.single (spAPar i0) 1) x y,
    hadd _ _ (hsum _ _ (hsum _ _ (hP _) (hP _)) (hP _)) (hP _),
    hadd _ _ (hsum _ _ (hP _) (hP _)) (hP _), hadd _ _ (hP _) (hP _),
    hFv _ h1, hFv _ (by rw [Pi.add_apply, h1, hx, add_zero]),
    hFv _ (by rw [Pi.add_apply, h1, hy, add_zero]),
    hFv _ (by rw [Pi.add_apply, Pi.add_apply, h1, hx, hy, add_zero, add_zero])]
  have hs := lagMat_add_self (Y i0 (spAPar i0) •
    (spARepMat N j : Matrix (Fin N) (Fin N) K))
  set s := Y i0 (spAPar i0) • (spARepMat N j : Matrix (Fin N) (Fin N) K)
  calc _ = (vecMulVec (Pi.single (spAPar i0) 1) (Pi.single (spAPar i0) 1) +
        vecMulVec (Pi.single (spAPar i0) 1 + x) (Pi.single (spAPar i0) 1 + x) +
        vecMulVec (Pi.single (spAPar i0) 1 + y) (Pi.single (spAPar i0) 1 + y) +
        vecMulVec (Pi.single (spAPar i0) 1 + x + y) (Pi.single (spAPar i0) 1 + x + y)) +
        ((s + s) + (s + s)) := by abel
    _ = _ := by rw [hs, add_zero, add_zero]

end Fix

end CFSG.SeitzReduction.SymplecticPilot
