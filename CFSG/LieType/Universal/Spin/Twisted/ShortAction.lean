module

public import CFSG.LieType.Universal.Spin.Twisted.Short

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

theorem coe_conj_one_add_ι_mul_ι (g : spinGroup Q) (w u : V) :
    (g : CliffordAlgebra Q) * (1 + ι Q w * ι Q u) * ↑g⁻¹ =
      1 + ι Q (spinAction Q g w) * ι Q (spinAction Q g u) := by
  rw [ι_spinAction, ι_spinAction, mul_add, add_mul, mul_one, coe_mul_coe_inv]
  simp only [mul_assoc, coe_inv_mul_coe_mul]

theorem spinAction_inv_apply_of_apply (g : spinGroup Q) {v w : V} (h : spinAction Q g w = v) :
    spinAction Q g⁻¹ v = w := by
  rw [← h, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one,
    id_eq]

end General

variable (n : ℕ) {K : Type*} [Field K] (b c : K)

@[expose] def polarPlane (w a : Fin 2 → K) : K :=
  2 * (w 0 * a 0) + b * (w 0 * a 1 + a 0 * w 1) + 2 * c * (w 1 * a 1)

@[expose] def planeNorm (w : Fin 2 → K) : K := w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2

theorem quadMinus_planeVec' (w : Fin 2 → K) :
    quadMinus n K b c (planeVec n w) = planeNorm b c w :=
  quadMinus_planeVec n b c w

theorem polarPlane_comm (w a : Fin 2 → K) : polarPlane b c w a = polarPlane b c a w := by
  simp only [polarPlane]
  ring

theorem polarPlane_self (w : Fin 2 → K) : polarPlane b c w w = 2 * planeNorm b c w := by
  simp only [polarPlane, planeNorm]
  ring

theorem polarPlane_add_left (w w' a : Fin 2 → K) :
    polarPlane b c (w + w') a = polarPlane b c w a + polarPlane b c w' a := by
  simp only [polarPlane, Pi.add_apply]
  ring

theorem polarPlane_smul_left (r : K) (w a : Fin 2 → K) :
    polarPlane b c (r • w) a = r * polarPlane b c w a := by
  simp only [polarPlane, Pi.smul_apply, smul_eq_mul]
  ring

theorem polarPlane_smul_right (r : K) (w a : Fin 2 → K) :
    polarPlane b c w (r • a) = r * polarPlane b c w a := by
  simp only [polarPlane, Pi.smul_apply, smul_eq_mul]
  ring

theorem polarPlane_neg_left (w a : Fin 2 → K) :
    polarPlane b c (-w) a = -polarPlane b c w a := by
  simp only [polarPlane, Pi.neg_apply]
  ring

theorem polarPlane_zero_left (a : Fin 2 → K) : polarPlane b c 0 a = 0 := by
  simp [polarPlane]

theorem planeNorm_smul (r : K) (w : Fin 2 → K) :
    planeNorm b c (r • w) = r ^ 2 * planeNorm b c w := by
  simp only [planeNorm, Pi.smul_apply, smul_eq_mul]
  ring

theorem planeNorm_neg (w : Fin 2 → K) : planeNorm b c (-w) = planeNorm b c w := by
  simp only [planeNorm, Pi.neg_apply]
  ring

theorem planeNorm_zero : planeNorm b c (0 : Fin 2 → K) = 0 := by
  simp [planeNorm]

variable {b c} in
theorem planeNorm_ne_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    planeNorm b c w ≠ 0 :=
  binary_ne_zero hirr hw

theorem planeVec_smul (r : K) (w : Fin 2 → K) : planeVec n (r • w) = r • planeVec n w := by
  funext v
  rcases v with i | i | t <;> simp [planeVec]

theorem planeVec_neg (w : Fin 2 → K) : planeVec n (-w) = -planeVec n w := by
  funext v
  rcases v with i | i | t <;> simp [planeVec]

theorem planeVec_sub (w w' : Fin 2 → K) : planeVec n (w - w') = planeVec n w - planeVec n w' := by
  funext v
  rcases v with i | i | t <;> simp [planeVec]

theorem polar_planeVec_planeVec (w a : Fin 2 → K) :
    polar (quadMinus n K b c) (planeVec n w) (planeVec n a) = polarPlane b c w a := by
  simp [polar_quadMinus, planeVec, polarPlane]

theorem polar_planeVec_eVec (w : Fin 2 → K) (i : Fin (n - 1)) :
    polar (quadMinus n K b c) (planeVec n w) (eVec n i) = 0 := by
  rw [polar_comm, polar_eVec_planeVec]

theorem polar_planeVec_fVec (w : Fin 2 → K) (i : Fin (n - 1)) :
    polar (quadMinus n K b c) (planeVec n w) (fVec n i) = 0 := by
  rw [polar_comm, polar_fVec_planeVec]

theorem polar_eVec_eVec (i j : Fin (n - 1)) :
    polar (quadMinus n K b c) (eVec n i) (eVec n j) = 0 := by
  simp [polar_quadMinus, eVec, Pi.single_apply]

theorem polar_fVec_fVec (i j : Fin (n - 1)) :
    polar (quadMinus n K b c) (fVec n i) (fVec n j) = 0 := by
  simp [polar_quadMinus, fVec, Pi.single_apply]

theorem polar_eVec_fVec (i j : Fin (n - 1)) :
    polar (quadMinus n K b c) (eVec n i) (fVec n j) = if i = j then 1 else 0 := by
  rw [fVec, polar_quadMinus_single_inr_inl]
  simp [eVec, Pi.single_apply, eq_comm]

theorem polar_fVec_eVec (i j : Fin (n - 1)) :
    polar (quadMinus n K b c) (fVec n i) (eVec n j) = if i = j then 1 else 0 := by
  rw [polar_comm, polar_eVec_fVec]
  simp [eq_comm]

@[expose] def wVec (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) : Vm n K :=
  l • eVec n i + planeVec n w + m • fVec n i

theorem wVec_apply_inl (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) (j : Fin (n - 1)) :
    wVec n i l w m (.inl j) = if j = i then l else 0 := by
  simp [wVec, eVec, fVec, planeVec, Pi.single_apply]

theorem wVec_apply_inr_inl (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) (j : Fin (n - 1)) :
    wVec n i l w m (.inr (.inl j)) = if j = i then m else 0 := by
  simp [wVec, eVec, fVec, planeVec, Pi.single_apply]

theorem wVec_apply_inr_inr (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) (t : Fin 2) :
    wVec n i l w m (.inr (.inr t)) = w t := by
  simp [wVec, eVec, fVec, planeVec]

theorem wVec_injective {i : Fin (n - 1)} {l l' : K} {w w' : Fin 2 → K} {m m' : K}
    (h : wVec n i l w m = wVec n i l' w' m') : l = l' ∧ w = w' ∧ m = m' := by
  refine ⟨?_, funext fun t => ?_, ?_⟩
  · simpa [wVec_apply_inl] using congrFun h (.inl i)
  · simpa [wVec_apply_inr_inr] using congrFun h (.inr (.inr t))
  · simpa [wVec_apply_inr_inl] using congrFun h (.inr (.inl i))

theorem wVec_eq_iff {i : Fin (n - 1)} {l l' : K} {w w' : Fin 2 → K} {m m' : K} :
    wVec n i l w m = wVec n i l' w' m' ↔ l = l' ∧ w = w' ∧ m = m' := by
  refine ⟨wVec_injective n, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  rfl

theorem wVec_eVec (i : Fin (n - 1)) : wVec n i (1 : K) 0 0 = eVec n i := by
  simp [wVec, planeVec_zero]

theorem wVec_fVec (i : Fin (n - 1)) : wVec n i (0 : K) 0 1 = fVec n i := by
  simp [wVec, planeVec_zero]

theorem wVec_planeVec (i : Fin (n - 1)) (w : Fin 2 → K) : wVec n i 0 w 0 = planeVec n w := by
  simp [wVec]

theorem wVec_smul (i : Fin (n - 1)) (r l : K) (w : Fin 2 → K) (m : K) :
    r • wVec n i l w m = wVec n i (r * l) (r • w) (r * m) := by
  simp only [wVec, smul_add, smul_smul, planeVec_smul]

theorem polar_wVec_eVec (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) :
    polar (quadMinus n K b c) (wVec n i l w m) (eVec n i) = m := by
  simp only [wVec, polar_add_left, polar_smul_left, polar_eVec_eVec, polar_planeVec_eVec,
    polar_fVec_eVec, ite_true, smul_eq_mul, mul_zero, mul_one, zero_add]

theorem polar_wVec_fVec (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) :
    polar (quadMinus n K b c) (wVec n i l w m) (fVec n i) = l := by
  simp only [wVec, polar_add_left, polar_smul_left, polar_eVec_fVec, polar_planeVec_fVec,
    polar_fVec_fVec, ite_true, smul_eq_mul, mul_zero, mul_one, add_zero]

theorem polar_wVec_planeVec (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) (a : Fin 2 → K) :
    polar (quadMinus n K b c) (wVec n i l w m) (planeVec n a) = polarPlane b c w a := by
  simp only [wVec, polar_add_left, polar_smul_left, polar_eVec_planeVec, polar_planeVec_planeVec,
    polar_fVec_planeVec, smul_eq_mul, mul_zero, add_zero, zero_add]

theorem quadMinus_wVec (i : Fin (n - 1)) (l : K) (w : Fin 2 → K) (m : K) :
    quadMinus n K b c (wVec n i l w m) = l * m + planeNorm b c w := by
  have h := QuadraticMap.map_add (quadMinus n K b c) (l • eVec n i + planeVec n w) (m • fVec n i)
  rw [QuadraticMap.map_add (quadMinus n K b c) (l • eVec n i) (planeVec n w)] at h
  rw [wVec, h]
  simp only [QuadraticMap.map_smul, quadMinus_eVec, quadMinus_fVec, quadMinus_planeVec',
    polar_add_left, polar_smul_left, polar_smul_right, polar_eVec_planeVec, polar_eVec_fVec,
    polar_planeVec_fVec, ite_true, smul_eq_mul]
  ring

variable {b c}

theorem coe_shortPosHom (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (a : Fin 2 → K) :
    (shortPosHom n hirr i (.ofAdd a) : CliffordAlgebra (quadMinus n K b c)) =
      1 + ι (quadMinus n K b c) (planeVec n a) * ι (quadMinus n K b c) (eVec n i) :=
  rfl

theorem coe_shortNegHom (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (a : Fin 2 → K) :
    (shortNegHom n hirr i (.ofAdd a) : CliffordAlgebra (quadMinus n K b c)) =
      1 + ι (quadMinus n K b c) (planeVec n a) * ι (quadMinus n K b c) (fVec n i) :=
  rfl

theorem spinAction_shortPosHom (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (a : Fin 2 → K) (v : Vm n K) :
    spinAction (quadMinus n K b c) (shortPosHom n hirr i (.ofAdd a)) v =
      v + polar (quadMinus n K b c) v (eVec n i) • planeVec n a -
        polar (quadMinus n K b c) v (planeVec n a) • eVec n i -
        (planeNorm b c a * polar (quadMinus n K b c) v (eVec n i)) • eVec n i := by
  rw [spinAction_apply_of_coe_eq _ (quadMinus_eVec n b c i) (polar_eVec_planeVec n b c i a)
    (coe_shortPosHom n hirr i a) v, quadMinus_planeVec']

theorem spinAction_shortNegHom (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (a : Fin 2 → K) (v : Vm n K) :
    spinAction (quadMinus n K b c) (shortNegHom n hirr i (.ofAdd a)) v =
      v + polar (quadMinus n K b c) v (fVec n i) • planeVec n a -
        polar (quadMinus n K b c) v (planeVec n a) • fVec n i -
        (planeNorm b c a * polar (quadMinus n K b c) v (fVec n i)) • fVec n i := by
  rw [spinAction_apply_of_coe_eq _ (quadMinus_fVec n b c i) (polar_fVec_planeVec n b c i a)
    (coe_shortNegHom n hirr i a) v, quadMinus_planeVec']

theorem spinAction_shortPosHom_wVec (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (a : Fin 2 → K) (l : K) (w : Fin 2 → K) (m : K) :
    spinAction (quadMinus n K b c) (shortPosHom n hirr i (.ofAdd a)) (wVec n i l w m) =
      wVec n i (l - polarPlane b c w a - planeNorm b c a * m) (w + m • a) m := by
  rw [spinAction_shortPosHom, polar_wVec_eVec, polar_wVec_planeVec]
  simp only [wVec, planeVec_add, planeVec_smul]
  module

theorem spinAction_shortNegHom_wVec (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (a : Fin 2 → K) (l : K) (w : Fin 2 → K) (m : K) :
    spinAction (quadMinus n K b c) (shortNegHom n hirr i (.ofAdd a)) (wVec n i l w m) =
      wVec n i l (w + l • a) (m - polarPlane b c w a - planeNorm b c a * l) := by
  rw [spinAction_shortNegHom, polar_wVec_fVec, polar_wVec_planeVec]
  simp only [wVec, planeVec_add, planeVec_smul]
  module

theorem spinAction_shortPosHom_of_polar (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (a : Fin 2 → K) {v : Vm n K}
    (h1 : polar (quadMinus n K b c) v (eVec n i) = 0)
    (h2 : polar (quadMinus n K b c) v (planeVec n a) = 0) :
    spinAction (quadMinus n K b c) (shortPosHom n hirr i (.ofAdd a)) v = v := by
  rw [spinAction_shortPosHom, h1, h2]
  simp

theorem spinAction_shortNegHom_of_polar (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (a : Fin 2 → K) {v : Vm n K}
    (h1 : polar (quadMinus n K b c) v (fVec n i) = 0)
    (h2 : polar (quadMinus n K b c) v (planeVec n a) = 0) :
    spinAction (quadMinus n K b c) (shortNegHom n hirr i (.ofAdd a)) v = v := by
  rw [spinAction_shortNegHom, h1, h2]
  simp

theorem spinAction_shortPosHom_eVec (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (a : Fin 2 → K) (j : Fin (n - 1)) :
    spinAction (quadMinus n K b c) (shortPosHom n hirr i (.ofAdd a)) (eVec n j) = eVec n j :=
  spinAction_shortPosHom_of_polar n hirr i a (polar_eVec_eVec n b c j i)
    (polar_eVec_planeVec n b c j a)

theorem spinAction_shortPosHom_fVec_of_ne (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : j ≠ i) (a : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortPosHom n hirr i (.ofAdd a)) (fVec n j) = fVec n j :=
  spinAction_shortPosHom_of_polar n hirr i a (by simp [polar_fVec_eVec, hij])
    (polar_fVec_planeVec n b c j a)

theorem spinAction_shortNegHom_fVec (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (a : Fin 2 → K) (j : Fin (n - 1)) :
    spinAction (quadMinus n K b c) (shortNegHom n hirr i (.ofAdd a)) (fVec n j) = fVec n j :=
  spinAction_shortNegHom_of_polar n hirr i a (polar_fVec_fVec n b c j i)
    (polar_fVec_planeVec n b c j a)

theorem spinAction_shortNegHom_eVec_of_ne (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : j ≠ i) (a : Fin 2 → K) :
    spinAction (quadMinus n K b c) (shortNegHom n hirr i (.ofAdd a)) (eVec n j) = eVec n j :=
  spinAction_shortNegHom_of_polar n hirr i a (by simp [polar_eVec_fVec, hij])
    (polar_eVec_planeVec n b c j a)

end CFSG.LieType.Universal.Spin.Twisted
