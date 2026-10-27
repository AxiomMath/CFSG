module

public import CFSG.CGT.Stroth77.Extension212Core

public section

namespace CFSG.CGT.Stroth77

variable {K : Fin 3 → ℕ}

theorem two_mul_add_one_zsmul_tw (hK : ∀ j, 1 ≤ K j) (y a b c : ℤ) :
    (2 * y + 1) • tw K a b c = tw K a b c := by
  rw [add_zsmul, one_zsmul, mul_comm, mul_zsmul, two_zsmul_tw hK, smul_zero, zero_add]

theorem two_mul_zsmul_tw (hK : ∀ j, 1 ≤ K j) (y a b c : ℤ) : (2 * y) • tw K a b c = 0 := by
  rw [mul_comm, mul_zsmul, two_zsmul_tw hK, smul_zero]

theorem forall_fin_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ j, P j := by
  intro j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

theorem basisChangeEquiv_conj {A : Type*} [AddCommGroup A] {ε δ : A →+ A} (hε : IsSmallDev ε)
    (hδ : IsSmallDev δ) (a : A →+ A) (x : A) :
    (basisChangeEquiv hε).symm ((a + δ) (basisChangeEquiv hε x)) =
      a x + (δ x + ε (a x) + a (ε x)) :=
  basisChange_conj hε hδ a x

@[expose] def AgreeB4 (K : Fin 3 → ℕ) (X Y : Torus K →+ Torus K) : Prop :=
  X (gen K 0) = Y (gen K 0) ∧ X ((2 : ℤ) • gen K 1) = Y ((2 : ℤ) • gen K 1) ∧
    X ((2 : ℤ) • gen K 2) = Y ((2 : ℤ) • gen K 2)

structure Profile4 (K : Fin 3 → ℕ) (aV aW aU aR : Torus K →+ Torus K) : Prop where
  nV : ∀ x y z : ℤ, aV (tw K x y z) = tw K x (x + y) (x + z)
  nW : ∀ x y z : ℤ, aW (tw K x y z) = tw K x (x + y) z
  nU : ∀ x y z : ℤ, aU (tw K x y z) = tw K x z y
  nR : ∀ x y z : ℤ, aR (tw K x y z) = tw K x z (y + z)
  fV0 : ∃ x y z : ℤ, aV (gen K 0) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z) • gen K 2
  fV1 : ∃ x y z : ℤ, aV (gen K 1) = x • gen K 0 + (2 * y + 1) • gen K 1 + (2 * z) • gen K 2
  fV2 : ∃ x y z : ℤ, aV (gen K 2) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z + 1) • gen K 2
  fW0 : ∃ x y z : ℤ, aW (gen K 0) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z) • gen K 2
  fW1 : ∃ x y z : ℤ, aW (gen K 1) = x • gen K 0 + (2 * y + 1) • gen K 1 + (2 * z) • gen K 2
  fW2 : ∃ x y z : ℤ, aW (gen K 2) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z + 1) • gen K 2
  fU0 : ∃ x y z : ℤ, aU (gen K 0) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z) • gen K 2
  fU1 : ∃ x y z : ℤ, aU (gen K 1) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z + 1) • gen K 2
  fU2 : ∃ x y z : ℤ, aU (gen K 2) = x • gen K 0 + (2 * y + 1) • gen K 1 + (2 * z) • gen K 2
  fR0 : ∃ x y z : ℤ, aR (gen K 0) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z) • gen K 2
  fR1 : ∃ x y z : ℤ, aR (gen K 1) = x • gen K 0 + (2 * y) • gen K 1 + (2 * z + 1) • gen K 2
  fR2 : ∃ x y z : ℤ, aR (gen K 2) = x • gen K 0 + (2 * y + 1) • gen K 1 + (2 * z + 1) • gen K 2

structure Twist4 (K : Fin 3 → ℕ) (aV aW aU aR aV' aW' aU' aR' : Torus K →+ Torus K) : Prop where
  V0 : aV' (gen K 0) = aV (gen K 0)
  V1 : aV' (gen K 1) = aV (gen K 1) + tw K 0 0 1
  V2 : aV' (gen K 2) = aV (gen K 2) + tw K 0 1 0
  W0 : aW' (gen K 0) = aW (gen K 0)
  W1 : aW' (gen K 1) = aW (gen K 1) + tw K 0 1 0
  W2 : aW' (gen K 2) = aW (gen K 2) + tw K 0 1 1
  U0 : aU' (gen K 0) = aU (gen K 0)
  U1 : aU' (gen K 1) = aU (gen K 1)
  U2 : aU' (gen K 2) = aU (gen K 2)
  R0 : aR' (gen K 0) = aR (gen K 0)
  R1 : aR' (gen K 1) = aR (gen K 1)
  R2 : aR' (gen K 2) = aR (gen K 2)

theorem dev_gen0_of_agreeB4 {X aX dX : Torus K →+ Torus K} (h : AgreeB4 K (aX + dX) aX) :
    dX (gen K 0) = 0 := by
  have h0 := h.1
  rw [AddMonoidHom.add_apply] at h0
  exact add_eq_left.mp h0

theorem isSmallDev_of_agreeB4 (hK : ∀ j, 1 ≤ K j) (hK1 : 2 ≤ K 1) (hK2 : 2 ≤ K 2)
    {aX dX : Torus K →+ Torus K} (h : AgreeB4 K (aX + dX) aX) : IsSmallDev dX := by
  have := isSmallDev_sub_idx4 hK hK1 hK2 h.1 h.2.1 h.2.2
  rwa [add_sub_cancel_left] at this

theorem pivots_idx4 (hK : ∀ j, 1 ≤ K j) (hK1 : 2 ≤ K 1) (hK2 : 2 ≤ K 2)
    {aV aW aU aR dV dW dU dR : Torus K →+ Torus K}
    (ha : SigmaFourRels aV aW aU aR) (hP : Profile4 K aV aW aU aR)
    (h : SigmaFourRels (aV + dV) (aW + dW) (aU + dU) (aR + dR))
    (hV : AgreeB4 K (aV + dV) aV) (hW : AgreeB4 K (aW + dW) aW) (hU : AgreeB4 K (aU + dU) aU)
    (hR : AgreeB4 K (aR + dR) aR) :
    ∃ q u4 r0 r3 r4 r5 : ℤ,
      dV (gen K 1) = tw K 0 r3 (q + r3) ∧
      dV (gen K 2) = tw K 0 (q + r0 + r3) (r0 + r3) ∧
      dW (gen K 1) = tw K 0 (q + r3) 0 ∧
      dW (gen K 2) = tw K 0 (q + r0 + r3) q ∧
      dU (gen K 1) = tw K r0 r5 u4 ∧
      dU (gen K 2) = tw K r0 u4 r5 ∧
      dR (gen K 1) = tw K r0 r5 (r4 + r5) ∧
      dR (gen K 2) = tw K r3 r4 r5 := by
  have sV := isSmallDev_of_agreeB4 hK hK1 hK2 hV
  have sW := isSmallDev_of_agreeB4 hK hK1 hK2 hW
  have sU := isSmallDev_of_agreeB4 hK hK1 hK2 hU
  have sR := isSmallDev_of_agreeB4 hK hK1 hK2 hR
  have dV0 := dev_gen0_of_agreeB4 (X := aV) hV
  have dW0 := dev_gen0_of_agreeB4 (X := aW) hW
  have dU0 := dev_gen0_of_agreeB4 (X := aU) hU
  have dR0 := dev_gen0_of_agreeB4 (X := aR) hR
  have L := linRels_of h ha sV sW sU sR
  obtain ⟨v0, v1, v2, hv1⟩ := exists_tw hK (sV.two_zsmul (gen K 1))
  obtain ⟨v3, v4, v5, hv2⟩ := exists_tw hK (sV.two_zsmul (gen K 2))
  obtain ⟨w0, w1, w2, hw1⟩ := exists_tw hK (sW.two_zsmul (gen K 1))
  obtain ⟨w3, w4, w5, hw2⟩ := exists_tw hK (sW.two_zsmul (gen K 2))
  obtain ⟨u0, u1, u2, hu1⟩ := exists_tw hK (sU.two_zsmul (gen K 1))
  obtain ⟨u3, u4, u5, hu2⟩ := exists_tw hK (sU.two_zsmul (gen K 2))
  obtain ⟨r0, r1, r2, hr1⟩ := exists_tw hK (sR.two_zsmul (gen K 1))
  obtain ⟨r3, r4, r5, hr2⟩ := exists_tw hK (sR.two_zsmul (gen K 2))
  obtain ⟨_, _, _, fV0⟩ := hP.fV0
  obtain ⟨_, _, _, fV1⟩ := hP.fV1
  obtain ⟨_, _, _, fV2⟩ := hP.fV2
  obtain ⟨_, _, _, fW0⟩ := hP.fW0
  obtain ⟨_, _, _, fW1⟩ := hP.fW1
  obtain ⟨_, _, _, fW2⟩ := hP.fW2
  obtain ⟨_, _, _, fU0⟩ := hP.fU0
  obtain ⟨_, _, _, fU1⟩ := hP.fU1
  obtain ⟨_, _, _, fU2⟩ := hP.fU2
  obtain ⟨_, _, _, fR0⟩ := hP.fR0
  obtain ⟨_, _, _, fR1⟩ := hP.fR1
  obtain ⟨_, _, _, fR2⟩ := hP.fR2
  have t1 := two_mul_add_one_zsmul_tw hK
  have t0 := two_mul_zsmul_tw hK
  have e1 := L.uv_sq (gen K 1)
  have e2 := L.uv_sq (gen K 2)
  have e3 := L.t_sq (gen K 1)
  have e4 := L.t_sq (gen K 2)
  have e5 := L.uv_comm_t (gen K 1)
  have e6 := L.uv_comm_t (gen K 2)
  have e7 := L.rho_cube (gen K 1)
  have e8 := L.rho_cube (gen K 2)
  have e9 := L.u_sq (gen K 1)
  have e10 := L.u_sq (gen K 2)
  have e11 := L.u_rho (gen K 1)
  have e12 := L.u_rho (gen K 2)
  have e13 := L.uv_rho (gen K 1)
  have e14 := L.uv_rho (gen K 2)
  have e15 := L.t_rho (gen K 1)
  have e16 := L.t_rho (gen K 2)
  have e17 := L.uv_comm_u (gen K 1)
  have e18 := L.uv_comm_u (gen K 2)
  have e19 := L.t_u (gen K 1)
  have e20 := L.t_u (gen K 2)
  simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add, map_zsmul,
    dV0, dW0, dU0, dR0, hv1, hv2, hw1, hw2, hu1, hu2, hr1, hr2, hP.nV, hP.nW, hP.nU, hP.nR,
    smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add, map_zsmul,
    dV0, dW0, dU0, dR0, hv1, hv2, hw1, hw2, hu1, hu2, hr1, hr2, hP.nV, hP.nW, hP.nU, hP.nR,
    smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add] at e11 e12 e13 e14 e15 e16 e17 e18
  simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add, map_zsmul,
    dV0, dW0, dU0, dR0, hv1, hv2, hw1, hw2, hu1, hu2, hr1, hr2, hP.nV, hP.nW, hP.nU, hP.nR,
    smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add] at e19 e20
  rw [tw_eq_zero_iff hK] at e1 e2 e3 e4 e7 e8 e9 e10 e11 e12
  rw [tw_eq_iff hK] at e5 e6 e13 e14 e15 e16 e17 e18 e19 e20
  obtain ⟨e1a, e1b, e1c⟩ := e1
  obtain ⟨e2a, e2b, e2c⟩ := e2
  obtain ⟨e3a, e3b, e3c⟩ := e3
  obtain ⟨e4a, e4b, e4c⟩ := e4
  obtain ⟨e5a, e5b, e5c⟩ := e5
  obtain ⟨e6a, e6b, e6c⟩ := e6
  obtain ⟨e7a, e7b, e7c⟩ := e7
  obtain ⟨e8a, e8b, e8c⟩ := e8
  obtain ⟨e9a, e9b, e9c⟩ := e9
  obtain ⟨e10a, e10b, e10c⟩ := e10
  obtain ⟨e11a, e11b, e11c⟩ := e11
  obtain ⟨e12a, e12b, e12c⟩ := e12
  obtain ⟨e13a, e13b, e13c⟩ := e13
  obtain ⟨e14a, e14b, e14c⟩ := e14
  obtain ⟨e15a, e15b, e15c⟩ := e15
  obtain ⟨e16a, e16b, e16c⟩ := e16
  obtain ⟨e17a, e17b, e17c⟩ := e17
  obtain ⟨e18a, e18b, e18c⟩ := e18
  obtain ⟨e19a, e19b, e19c⟩ := e19
  obtain ⟨e20a, e20b, e20c⟩ := e20
  have p_v0 : 2 ∣ v0 := by clear * - e1b; omega
  have p_v1 : 2 ∣ v1 - r3 := by clear * - e2b e9a e11a e13c e14b e15b e15c e17b; omega
  have p_v2 : 2 ∣ v2 - w5 - r3 := by clear * - e2b e9a e11a e14b e15b e15c e17b; omega
  have p_v3 : 2 ∣ v3 := by clear * - e2b; omega
  have p_v4 : 2 ∣ v4 - w5 - r0 - r3 := by clear * - e2b e14b e15b e15c; omega
  have p_v5 : 2 ∣ v5 - r0 - r3 := by clear * - e9a e11a e13b e14b e14c e15c e17b; omega
  have p_w0 : 2 ∣ w0 := by clear * - e3b; omega
  have p_w1 : 2 ∣ w1 - w5 - r3 := by clear * - e2b e14b e14c e15b; omega
  have p_w2 : 2 ∣ w2 := by clear * - e2b e9a e11a e13b e15b e17b; omega
  have p_w3 : 2 ∣ w3 := by clear * - e4b; omega
  have p_w4 : 2 ∣ w4 - w5 - r0 - r3 := by clear * - e2b e9a e11a e13b e14b e15b e15c e17b; omega
  have p_u0 : 2 ∣ u0 - r0 := by clear * - e9a e11a; omega
  have p_u1 : 2 ∣ u1 - r5 := by clear * - e7b e7c e9c e11b; omega
  have p_u2 : 2 ∣ u2 - u4 := by clear * - e9b; omega
  have p_u3 : 2 ∣ u3 - r0 := by clear * - e11a; omega
  have p_u5 : 2 ∣ u5 - r5 := by clear * - e7b e7c e11b; omega
  have p_r1 : 2 ∣ r1 - r5 := by clear * - e7b e7c; omega
  have p_r2 : 2 ∣ r2 - r4 - r5 := by clear * - e7b; omega
  exact ⟨w5, u4, r0, r3, r4, r5,
    hv1.trans (tw_congr hK (by clear * - p_v0; omega) (by clear * - p_v1; omega)
      (by clear * - p_v2; omega)),
    hv2.trans (tw_congr hK (by clear * - p_v3; omega) (by clear * - p_v4; omega)
      (by clear * - p_v5; omega)),
    hw1.trans (tw_congr hK (by clear * - p_w0; omega) (by clear * - p_w1; omega)
      (by clear * - p_w2; omega)),
    hw2.trans (tw_congr hK (by clear * - p_w3; omega) (by clear * - p_w4; omega)
      (by omega)),
    hu1.trans (tw_congr hK (by clear * - p_u0; omega) (by clear * - p_u1; omega)
      (by clear * - p_u2; omega)),
    hu2.trans (tw_congr hK (by clear * - p_u3; omega) (by omega)
      (by clear * - p_u5; omega)),
    hr1.trans (tw_congr hK (by omega) (by clear * - p_r1; omega)
      (by clear * - p_r2; omega)),
    hr2.trans (tw_congr hK (by omega) (by omega)
      (by omega))⟩

theorem final_idx4 (hK : ∀ j, 1 ≤ K j) (hK1 : 2 ≤ K 1) (hK2 : 2 ≤ K 2)
    {aV aW aU aR aV' aW' aU' aR' dV dW dU dR : Torus K →+ Torus K}
    (hP : Profile4 K aV aW aU aR) (hT : Twist4 K aV aW aU aR aV' aW' aU' aR')
    (sV : IsSmallDev dV) (sW : IsSmallDev dW) (sU : IsSmallDev dU) (sR : IsSmallDev dR)
    (dV0 : dV (gen K 0) = 0) (dW0 : dW (gen K 0) = 0) (dU0 : dU (gen K 0) = 0)
    (dR0 : dR (gen K 0) = 0) {q u4 r0 r3 r4 r5 : ℤ}
    (hv1 : dV (gen K 1) = tw K 0 r3 (q + r3)) (hv2 : dV (gen K 2) = tw K 0 (q + r0 + r3) (r0 + r3))
    (hw1 : dW (gen K 1) = tw K 0 (q + r3) 0) (hw2 : dW (gen K 2) = tw K 0 (q + r0 + r3) q)
    (hu1 : dU (gen K 1) = tw K r0 r5 u4) (hu2 : dU (gen K 2) = tw K r0 u4 r5)
    (hr1 : dR (gen K 1) = tw K r0 r5 (r4 + r5)) (hr2 : dR (gen K 2) = tw K r3 r4 r5) :
    ∃ φ : Torus K ≃+ Torus K,
      (∀ j, φ.symm ((aV + dV) (φ (gen K j))) = aV (gen K j) ∧
        φ.symm ((aW + dW) (φ (gen K j))) = aW (gen K j) ∧
        φ.symm ((aU + dU) (φ (gen K j))) = aU (gen K j) ∧
        φ.symm ((aR + dR) (φ (gen K j))) = aR (gen K j)) ∨
      (∀ j, φ.symm ((aV + dV) (φ (gen K j))) = aV' (gen K j) ∧
        φ.symm ((aW + dW) (φ (gen K j))) = aW' (gen K j) ∧
        φ.symm ((aU + dU) (φ (gen K j))) = aU' (gen K j) ∧
        φ.symm ((aR + dR) (φ (gen K j))) = aR' (gen K j)) := by
  obtain ⟨_, _, _, fV0⟩ := hP.fV0
  obtain ⟨_, _, _, fV1⟩ := hP.fV1
  obtain ⟨_, _, _, fV2⟩ := hP.fV2
  obtain ⟨_, _, _, fW0⟩ := hP.fW0
  obtain ⟨_, _, _, fW1⟩ := hP.fW1
  obtain ⟨_, _, _, fW2⟩ := hP.fW2
  obtain ⟨_, _, _, fU0⟩ := hP.fU0
  obtain ⟨_, _, _, fU1⟩ := hP.fU1
  obtain ⟨_, _, _, fU2⟩ := hP.fU2
  obtain ⟨_, _, _, fR0⟩ := hP.fR0
  obtain ⟨_, _, _, fR1⟩ := hP.fR1
  obtain ⟨_, _, _, fR2⟩ := hP.fR2
  have t1 := two_mul_add_one_zsmul_tw hK
  have t0 := two_mul_zsmul_tw hK
  have hε := isSmallDev_eps4 hK hK1 hK2 r3 u4 (u4 + r4 + r5) (r0 + r3) (u4 + r4) 0
  have ε0 := eps4_gen0 hK r3 u4 (u4 + r4 + r5) (r0 + r3) (u4 + r4) 0
  have ε1 := eps4_gen1 hK r3 u4 (u4 + r4 + r5) (r0 + r3) (u4 + r4) 0
  have ε2 := eps4_gen2 hK r3 u4 (u4 + r4 + r5) (r0 + r3) (u4 + r4) 0
  refine ⟨basisChangeEquiv hε, ?_⟩
  rcases Int.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine forall_fin_three ?_ ?_ ?_ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [basisChangeEquiv_conj hε (by assumption), add_eq_left] <;>
    simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add, map_zsmul,
      dV0, dW0, dU0, dR0, hv1, hv2, hw1, hw2, hu1, hu2, hr1, hr2, hP.nV, hP.nW, hP.nU, hP.nR,
      ε0, ε1, ε2, smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add, map_zero] <;>
    first
    | done
    | (rw [tw_eq_zero_iff hK]; refine ⟨?_, ?_, ?_⟩ <;> omega)
  · right
    refine forall_fin_three ?_ ?_ ?_ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hT.V0, hT.V1, hT.V2, hT.W0, hT.W1, hT.W2, hT.U0, hT.U1, hT.U2, hT.R0, hT.R1,
      hT.R2] <;>
    rw [basisChangeEquiv_conj hε (by assumption)] <;>
    first
    | (rw [add_right_inj]
       simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add,
         map_zsmul, dV0, dW0, dU0, dR0, hv1, hv2, hw1, hw2, hu1, hu2, hr1, hr2, hP.nV, hP.nW,
         hP.nU, hP.nR, ε0, ε1, ε2, smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add,
         map_zero]
       rw [tw_eq_iff hK]
       refine ⟨?_, ?_, ?_⟩ <;> omega)
    | (rw [add_eq_left]
       simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add,
         map_zsmul, dV0, dW0, dU0, dR0, hv1, hv2, hw1, hw2, hu1, hu2, hr1, hr2, hP.nV, hP.nW,
         hP.nU, hP.nR, ε0, ε1, ε2, smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add,
         map_zero]
       first
       | done
       | (rw [tw_eq_zero_iff hK]; refine ⟨?_, ?_, ?_⟩ <;> omega))

theorem classify_idx4 (hK : ∀ j, 1 ≤ K j) (hK1 : 2 ≤ K 1) (hK2 : 2 ≤ K 2)
    {aV aW aU aR aV' aW' aU' aR' V W U R : Torus K →+ Torus K}
    (ha : SigmaFourRels aV aW aU aR) (hP : Profile4 K aV aW aU aR)
    (hT : Twist4 K aV aW aU aR aV' aW' aU' aR') (h : SigmaFourRels V W U R)
    (hV : AgreeB4 K V aV) (hW : AgreeB4 K W aW) (hU : AgreeB4 K U aU) (hR : AgreeB4 K R aR) :
    ∃ φ : Torus K ≃+ Torus K,
      (∀ j, φ.symm (V (φ (gen K j))) = aV (gen K j) ∧ φ.symm (W (φ (gen K j))) = aW (gen K j) ∧
        φ.symm (U (φ (gen K j))) = aU (gen K j) ∧ φ.symm (R (φ (gen K j))) = aR (gen K j)) ∨
      (∀ j, φ.symm (V (φ (gen K j))) = aV' (gen K j) ∧ φ.symm (W (φ (gen K j))) = aW' (gen K j) ∧
        φ.symm (U (φ (gen K j))) = aU' (gen K j) ∧ φ.symm (R (φ (gen K j))) = aR' (gen K j)) := by
  obtain ⟨dV, rfl⟩ : ∃ d, V = aV + d := ⟨V - aV, (add_sub_cancel_hom V aV).symm⟩
  obtain ⟨dW, rfl⟩ : ∃ d, W = aW + d := ⟨W - aW, (add_sub_cancel_hom W aW).symm⟩
  obtain ⟨dU, rfl⟩ : ∃ d, U = aU + d := ⟨U - aU, (add_sub_cancel_hom U aU).symm⟩
  obtain ⟨dR, rfl⟩ : ∃ d, R = aR + d := ⟨R - aR, (add_sub_cancel_hom R aR).symm⟩
  obtain ⟨q, u4, r0, r3, r4, r5, hv1, hv2, hw1, hw2, hu1, hu2, hr1, hr2⟩ :=
    pivots_idx4 hK hK1 hK2 ha hP h hV hW hU hR
  exact final_idx4 hK hK1 hK2 hP hT (isSmallDev_of_agreeB4 hK hK1 hK2 hV)
    (isSmallDev_of_agreeB4 hK hK1 hK2 hW) (isSmallDev_of_agreeB4 hK hK1 hK2 hU)
    (isSmallDev_of_agreeB4 hK hK1 hK2 hR) (dev_gen0_of_agreeB4 (X := aV) hV)
    (dev_gen0_of_agreeB4 (X := aW) hW) (dev_gen0_of_agreeB4 (X := aU) hU)
    (dev_gen0_of_agreeB4 (X := aR) hR) hv1 hv2 hw1 hw2 hu1 hu2 hr1 hr2

@[expose] def AgreeB2 (K : Fin 3 → ℕ) (X Y : Torus K →+ Torus K) : Prop :=
  X ((2 : ℤ) • gen K 0) = Y ((2 : ℤ) • gen K 0) ∧ X (gen K 1) = Y (gen K 1) ∧
    X (gen K 2) = Y (gen K 2)

structure Profile2 (K : Fin 3 → ℕ) (aV aW aU aR : Torus K →+ Torus K) : Prop where
  nV : ∀ x y z : ℤ, aV (tw K x y z) = tw K x (x + y) (x + z)
  nW : ∀ x y z : ℤ, aW (tw K x y z) = tw K x (x + y) z
  nU : ∀ x y z : ℤ, aU (tw K x y z) = tw K x z y
  nR : ∀ x y z : ℤ, aR (tw K x y z) = tw K x z (y + z)
  fV0 : ∃ x y z : ℤ, aV (gen K 0) = (2 * x + 1) • gen K 0 + y • gen K 1 + z • gen K 2
  fV1 : ∃ x y z : ℤ, aV (gen K 1) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2
  fV2 : ∃ x y z : ℤ, aV (gen K 2) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2
  fW0 : ∃ x y z : ℤ, aW (gen K 0) = (2 * x + 1) • gen K 0 + y • gen K 1 + z • gen K 2
  fW1 : ∃ x y z : ℤ, aW (gen K 1) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2
  fW2 : ∃ x y z : ℤ, aW (gen K 2) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2
  fU0 : ∃ x y z : ℤ, aU (gen K 0) = (2 * x + 1) • gen K 0 + y • gen K 1 + z • gen K 2
  fU1 : ∃ x y z : ℤ, aU (gen K 1) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2
  fU2 : ∃ x y z : ℤ, aU (gen K 2) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2
  fR0 : ∃ x y z : ℤ, aR (gen K 0) = (2 * x + 1) • gen K 0 + y • gen K 1 + z • gen K 2
  fR1 : ∃ x y z : ℤ, aR (gen K 1) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2
  fR2 : ∃ x y z : ℤ, aR (gen K 2) = (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2

structure Twist2 (K : Fin 3 → ℕ) (aV aW aU aR aV' aW' aU' aR' : Torus K →+ Torus K) : Prop where
  V0 : aV' (gen K 0) = aV (gen K 0) + tw K 0 1 0
  V1 : aV' (gen K 1) = aV (gen K 1)
  V2 : aV' (gen K 2) = aV (gen K 2)
  W0 : aW' (gen K 0) = aW (gen K 0) + tw K 0 0 1
  W1 : aW' (gen K 1) = aW (gen K 1)
  W2 : aW' (gen K 2) = aW (gen K 2)
  U0 : aU' (gen K 0) = aU (gen K 0) + tw K 1 0 0
  U1 : aU' (gen K 1) = aU (gen K 1)
  U2 : aU' (gen K 2) = aU (gen K 2)
  R0 : aR' (gen K 0) = aR (gen K 0)
  R1 : aR' (gen K 1) = aR (gen K 1)
  R2 : aR' (gen K 2) = aR (gen K 2)

theorem dev_gen12_of_agreeB2 {X aX dX : Torus K →+ Torus K} (h : AgreeB2 K (aX + dX) aX) :
    dX (gen K 1) = 0 ∧ dX (gen K 2) = 0 := by
  have h1 := h.2.1
  have h2 := h.2.2
  rw [AddMonoidHom.add_apply] at h1 h2
  exact ⟨add_eq_left.mp h1, add_eq_left.mp h2⟩

theorem isSmallDev_of_agreeB2 (hK : ∀ j, 1 ≤ K j) (hK0 : 2 ≤ K 0)
    {aX dX : Torus K →+ Torus K} (h : AgreeB2 K (aX + dX) aX) : IsSmallDev dX := by
  have := isSmallDev_sub_idx2 hK hK0 h.1 h.2.1 h.2.2
  rwa [add_sub_cancel_left] at this

theorem pivots_idx2 (hK : ∀ j, 1 ≤ K j) (hK0 : 2 ≤ K 0)
    {aV aW aU aR dV dW dU dR : Torus K →+ Torus K}
    (ha : SigmaFourRels aV aW aU aR) (hP : Profile2 K aV aW aU aR)
    (h : SigmaFourRels (aV + dV) (aW + dW) (aU + dU) (aR + dR))
    (hV : AgreeB2 K (aV + dV) aV) (hW : AgreeB2 K (aW + dW) aW) (hU : AgreeB2 K (aU + dU) aU)
    (hR : AgreeB2 K (aR + dR) aR) :
    ∃ q w1 r1 r2 : ℤ, dV (gen K 0) = tw K 0 (w1 + q) w1 ∧ dW (gen K 0) = tw K 0 w1 q ∧
      dU (gen K 0) = tw K q r1 r1 ∧ dR (gen K 0) = tw K 0 r1 r2 := by
  have sV := isSmallDev_of_agreeB2 hK hK0 hV
  have sW := isSmallDev_of_agreeB2 hK hK0 hW
  have sU := isSmallDev_of_agreeB2 hK hK0 hU
  have sR := isSmallDev_of_agreeB2 hK hK0 hR
  obtain ⟨dV1, dV2⟩ := dev_gen12_of_agreeB2 (X := aV) hV
  obtain ⟨dW1, dW2⟩ := dev_gen12_of_agreeB2 (X := aW) hW
  obtain ⟨dU1, dU2⟩ := dev_gen12_of_agreeB2 (X := aU) hU
  obtain ⟨dR1, dR2⟩ := dev_gen12_of_agreeB2 (X := aR) hR
  have L := linRels_of h ha sV sW sU sR
  obtain ⟨v0, v1, v2, hv⟩ := exists_tw hK (sV.two_zsmul (gen K 0))
  obtain ⟨w0, w1, w2, hw⟩ := exists_tw hK (sW.two_zsmul (gen K 0))
  obtain ⟨u0, u1, u2, hu⟩ := exists_tw hK (sU.two_zsmul (gen K 0))
  obtain ⟨r0, r1, r2, hr⟩ := exists_tw hK (sR.two_zsmul (gen K 0))
  obtain ⟨_, _, _, fV0⟩ := hP.fV0
  obtain ⟨_, _, _, fV1⟩ := hP.fV1
  obtain ⟨_, _, _, fV2⟩ := hP.fV2
  obtain ⟨_, _, _, fW0⟩ := hP.fW0
  obtain ⟨_, _, _, fW1⟩ := hP.fW1
  obtain ⟨_, _, _, fW2⟩ := hP.fW2
  obtain ⟨_, _, _, fU0⟩ := hP.fU0
  obtain ⟨_, _, _, fU1⟩ := hP.fU1
  obtain ⟨_, _, _, fU2⟩ := hP.fU2
  obtain ⟨_, _, _, fR0⟩ := hP.fR0
  obtain ⟨_, _, _, fR1⟩ := hP.fR1
  obtain ⟨_, _, _, fR2⟩ := hP.fR2
  have t1 := two_mul_add_one_zsmul_tw hK
  have t0 := two_mul_zsmul_tw hK
  have e1 := L.uv_sq (gen K 0)
  have e2 := L.t_sq (gen K 0)
  have e3 := L.uv_comm_t (gen K 0)
  have e4 := L.rho_cube (gen K 0)
  have e5 := L.u_sq (gen K 0)
  have e6 := L.u_rho (gen K 0)
  have e7 := L.uv_rho (gen K 0)
  have e8 := L.t_rho (gen K 0)
  have e9 := L.uv_comm_u (gen K 0)
  have e10 := L.t_u (gen K 0)
  simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add, map_zsmul,
    dV1, dV2, dW1, dW2, dU1, dU2, dR1, dR2, hv, hw, hu, hr, hP.nV, hP.nW, hP.nU, hP.nR,
    smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  rw [tw_eq_zero_iff hK] at e1 e2 e4 e5 e6
  rw [tw_eq_iff hK] at e3 e7 e8 e9 e10
  obtain ⟨e1a, e1b, e1c⟩ := e1
  obtain ⟨e2a, e2b, e2c⟩ := e2
  obtain ⟨e3a, e3b, e3c⟩ := e3
  obtain ⟨e4a, e4b, e4c⟩ := e4
  obtain ⟨e5a, e5b, e5c⟩ := e5
  obtain ⟨e6a, e6b, e6c⟩ := e6
  obtain ⟨e7a, e7b, e7c⟩ := e7
  obtain ⟨e8a, e8b, e8c⟩ := e8
  obtain ⟨e9a, e9b, e9c⟩ := e9
  obtain ⟨e10a, e10b, e10c⟩ := e10
  have p_v0 : 2 ∣ v0 := by clear * - e1b; omega
  have p_v1 : 2 ∣ v1 - w1 - u0 := by clear * - e4a e7b e9b; omega
  have p_v2 : 2 ∣ v2 - w1 := by clear * - e4a e7b; omega
  have p_w0 : 2 ∣ w0 := by clear * - e2b; omega
  have p_w2 : 2 ∣ w2 - u0 := by clear * - e7c e9b; omega
  have p_u1 : 2 ∣ u1 - r1 := by clear * - e5b e6c; omega
  have p_u2 : 2 ∣ u2 - r1 := by clear * - e6c; omega
  have p_r0 : 2 ∣ r0 := by clear * - e4a; omega
  exact ⟨u0, w1, r1, r2,
    hv.trans (tw_congr hK (by clear * - p_v0; omega) (by clear * - p_v1; omega)
      (by clear * - p_v2; omega)),
    hw.trans (tw_congr hK (by clear * - p_w0; omega) (by omega) (by clear * - p_w2; omega)),
    hu.trans (tw_congr hK (by omega) (by clear * - p_u1; omega) (by clear * - p_u2; omega)),
    hr.trans (tw_congr hK (by clear * - p_r0; omega) (by omega) (by omega))⟩

theorem final_idx2 (hK : ∀ j, 1 ≤ K j) (hK0 : 2 ≤ K 0)
    {aV aW aU aR aV' aW' aU' aR' dV dW dU dR : Torus K →+ Torus K}
    (hP : Profile2 K aV aW aU aR) (hT : Twist2 K aV aW aU aR aV' aW' aU' aR')
    (sV : IsSmallDev dV) (sW : IsSmallDev dW) (sU : IsSmallDev dU) (sR : IsSmallDev dR)
    (dV1 : dV (gen K 1) = 0) (dV2 : dV (gen K 2) = 0) (dW1 : dW (gen K 1) = 0)
    (dW2 : dW (gen K 2) = 0) (dU1 : dU (gen K 1) = 0) (dU2 : dU (gen K 2) = 0)
    (dR1 : dR (gen K 1) = 0) (dR2 : dR (gen K 2) = 0) {q w1 r1 r2 : ℤ}
    (hv : dV (gen K 0) = tw K 0 (w1 + q) w1) (hw : dW (gen K 0) = tw K 0 w1 q)
    (hu : dU (gen K 0) = tw K q r1 r1) (hr : dR (gen K 0) = tw K 0 r1 r2) :
    ∃ φ : Torus K ≃+ Torus K,
      (∀ j, φ.symm ((aV + dV) (φ (gen K j))) = aV (gen K j) ∧
        φ.symm ((aW + dW) (φ (gen K j))) = aW (gen K j) ∧
        φ.symm ((aU + dU) (φ (gen K j))) = aU (gen K j) ∧
        φ.symm ((aR + dR) (φ (gen K j))) = aR (gen K j)) ∨
      (∀ j, φ.symm ((aV + dV) (φ (gen K j))) = aV' (gen K j) ∧
        φ.symm ((aW + dW) (φ (gen K j))) = aW' (gen K j) ∧
        φ.symm ((aU + dU) (φ (gen K j))) = aU' (gen K j) ∧
        φ.symm ((aR + dR) (φ (gen K j))) = aR' (gen K j)) := by
  obtain ⟨_, _, _, fV0⟩ := hP.fV0
  obtain ⟨_, _, _, fV1⟩ := hP.fV1
  obtain ⟨_, _, _, fV2⟩ := hP.fV2
  obtain ⟨_, _, _, fW0⟩ := hP.fW0
  obtain ⟨_, _, _, fW1⟩ := hP.fW1
  obtain ⟨_, _, _, fW2⟩ := hP.fW2
  obtain ⟨_, _, _, fU0⟩ := hP.fU0
  obtain ⟨_, _, _, fU1⟩ := hP.fU1
  obtain ⟨_, _, _, fU2⟩ := hP.fU2
  obtain ⟨_, _, _, fR0⟩ := hP.fR0
  obtain ⟨_, _, _, fR1⟩ := hP.fR1
  obtain ⟨_, _, _, fR2⟩ := hP.fR2
  have t1 := two_mul_add_one_zsmul_tw hK
  have t0 := two_mul_zsmul_tw hK
  have hε := isSmallDev_eps2 hK hK0 w1 r2 (r1 + r2)
  have ε0 := eps2_gen0 hK w1 r2 (r1 + r2)
  have ε1 := eps2_gen1 hK w1 r2 (r1 + r2)
  have ε2 := eps2_gen2 hK w1 r2 (r1 + r2)
  refine ⟨basisChangeEquiv hε, ?_⟩
  rcases Int.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine forall_fin_three ?_ ?_ ?_ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [basisChangeEquiv_conj hε (by assumption), add_eq_left] <;>
    simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add, map_zsmul,
      dV1, dV2, dW1, dW2, dU1, dU2, dR1, dR2, hv, hw, hu, hr, hP.nV, hP.nW, hP.nU, hP.nR,
      ε0, ε1, ε2, smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add, map_zero] <;>
    first
    | done
    | (rw [tw_eq_zero_iff hK]; refine ⟨?_, ?_, ?_⟩ <;> omega)
  · right
    refine forall_fin_three ?_ ?_ ?_ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [hT.V0, hT.V1, hT.V2, hT.W0, hT.W1, hT.W2, hT.U0, hT.U1, hT.U2, hT.R0, hT.R1,
      hT.R2] <;>
    rw [basisChangeEquiv_conj hε (by assumption)] <;>
    first
    | (rw [add_right_inj]
       simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add,
         map_zsmul, dV1, dV2, dW1, dW2, dU1, dU2, dR1, dR2, hv, hw, hu, hr, hP.nV, hP.nW,
         hP.nU, hP.nR, ε0, ε1, ε2, smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add,
         map_zero]
       rw [tw_eq_iff hK]
       refine ⟨?_, ?_, ?_⟩ <;> omega)
    | (rw [add_eq_left]
       simp only [fV0, fV1, fV2, fW0, fW1, fW2, fU0, fU1, fU2, fR0, fR1, fR2, map_add,
         map_zsmul, dV1, dV2, dW1, dW2, dU1, dU2, dR1, dR2, hv, hw, hu, hr, hP.nV, hP.nW,
         hP.nU, hP.nR, ε0, ε1, ε2, smul_zero, smul_add, t1, t0, add_zero, zero_add, tw_add,
         map_zero]
       first
       | done
       | (rw [tw_eq_zero_iff hK]; refine ⟨?_, ?_, ?_⟩ <;> omega))

theorem classify_idx2 (hK : ∀ j, 1 ≤ K j) (hK0 : 2 ≤ K 0)
    {aV aW aU aR aV' aW' aU' aR' V W U R : Torus K →+ Torus K}
    (ha : SigmaFourRels aV aW aU aR) (hP : Profile2 K aV aW aU aR)
    (hT : Twist2 K aV aW aU aR aV' aW' aU' aR') (h : SigmaFourRels V W U R)
    (hV : AgreeB2 K V aV) (hW : AgreeB2 K W aW) (hU : AgreeB2 K U aU) (hR : AgreeB2 K R aR) :
    ∃ φ : Torus K ≃+ Torus K,
      (∀ j, φ.symm (V (φ (gen K j))) = aV (gen K j) ∧ φ.symm (W (φ (gen K j))) = aW (gen K j) ∧
        φ.symm (U (φ (gen K j))) = aU (gen K j) ∧ φ.symm (R (φ (gen K j))) = aR (gen K j)) ∨
      (∀ j, φ.symm (V (φ (gen K j))) = aV' (gen K j) ∧ φ.symm (W (φ (gen K j))) = aW' (gen K j) ∧
        φ.symm (U (φ (gen K j))) = aU' (gen K j) ∧ φ.symm (R (φ (gen K j))) = aR' (gen K j)) := by
  obtain ⟨dV, rfl⟩ : ∃ d, V = aV + d := ⟨V - aV, (add_sub_cancel_hom V aV).symm⟩
  obtain ⟨dW, rfl⟩ : ∃ d, W = aW + d := ⟨W - aW, (add_sub_cancel_hom W aW).symm⟩
  obtain ⟨dU, rfl⟩ : ∃ d, U = aU + d := ⟨U - aU, (add_sub_cancel_hom U aU).symm⟩
  obtain ⟨dR, rfl⟩ : ∃ d, R = aR + d := ⟨R - aR, (add_sub_cancel_hom R aR).symm⟩
  obtain ⟨q, w1, r1, r2, hv, hw, hu, hr⟩ := pivots_idx2 hK hK0 ha hP h hV hW hU hR
  obtain ⟨dV1, dV2⟩ := dev_gen12_of_agreeB2 (X := aV) hV
  obtain ⟨dW1, dW2⟩ := dev_gen12_of_agreeB2 (X := aW) hW
  obtain ⟨dU1, dU2⟩ := dev_gen12_of_agreeB2 (X := aU) hU
  obtain ⟨dR1, dR2⟩ := dev_gen12_of_agreeB2 (X := aR) hR
  exact final_idx2 hK hK0 hP hT (isSmallDev_of_agreeB2 hK hK0 hV)
    (isSmallDev_of_agreeB2 hK hK0 hW) (isSmallDev_of_agreeB2 hK hK0 hU)
    (isSmallDev_of_agreeB2 hK hK0 hR) dV1 dV2 dW1 dW2 dU1 dU2 dR1 dR2 hv hw hu hr

end CFSG.CGT.Stroth77
