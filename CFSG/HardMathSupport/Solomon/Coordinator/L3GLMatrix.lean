module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalHeis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem l3gl_cayleyHamilton_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M ^ 3 - M.trace • M ^ 2 + M.adjugate.trace • M - M.det • (1 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  rw [Matrix.eta_fin_three M]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.adjugate_fin_three, Matrix.det_fin_three, Matrix.trace_fin_three] <;>
    ring

variable {K : Type} [Field K]

local notation "S" => Matrix.GeneralLinearGroup.scalar (Fin 3)

theorem l3gl_det_scalar (c : Kˣ) :
    ((S c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = (c : K) ^ 3 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem l3gl_scalar_pow_three {c : Kˣ} (h : (c : K) ^ 3 = 1) : (S c : GL (Fin 3) K) ^ 3 = 1 := by
  rw [← map_pow, show c ^ 3 = 1 from Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one]),
    map_one]

theorem l3gl_trace_eq_zero {X W : GL (Fin 3) K} {c : Kˣ} (hc : c ≠ 1)
    (h : X * W * X⁻¹ = S c * W) : (W : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  have ht := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).trace) h
  simp only [Units.val_mul] at ht
  rw [Matrix.trace_units_conj, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    smul_eq_mul] at ht
  have hc' : (c : K) ≠ 1 := fun h1 => hc (Units.ext h1)
  have : ((c : K) - 1) * (W : Matrix (Fin 3) (Fin 3) K).trace = 0 := by linear_combination -ht
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc')

theorem l3gl_pow_three_eq_one {X W : GL (Fin 3) K} {c : Kˣ} (hc : c ≠ 1)
    (h : X * W * X⁻¹ = S c * W) (hdet : (W : Matrix (Fin 3) (Fin 3) K).det = 1) : W ^ 3 = 1 := by
  have htr := l3gl_trace_eq_zero hc h
  have h' : X * W⁻¹ * X⁻¹ = S c⁻¹ * W⁻¹ := by
    have h1 : (X * W * X⁻¹)⁻¹ = (S c * W)⁻¹ := by rw [h]
    have e1 : (X * W * X⁻¹)⁻¹ = X * W⁻¹ * X⁻¹ := by group
    rw [e1, _root_.mul_inv_rev, ← map_inv] at h1
    rw [h1]
    exact (Matrix.GeneralLinearGroup.scalar_commute c⁻¹ W⁻¹).symm
  have htr' : ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 0 :=
    l3gl_trace_eq_zero (inv_ne_one.2 hc) h'
  have hadj : (W : Matrix (Fin 3) (Fin 3) K).adjugate =
      (W : Matrix (Fin 3) (Fin 3) K).det • ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    calc (W : Matrix (Fin 3) (Fin 3) K).adjugate
        = (W : Matrix (Fin 3) (Fin 3) K).adjugate *
            ((W : Matrix (Fin 3) (Fin 3) K) * ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = ((W : Matrix (Fin 3) (Fin 3) K).adjugate * (W : Matrix (Fin 3) (Fin 3) K)) *
            ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hCH := l3gl_cayleyHamilton_three (W : Matrix (Fin 3) (Fin 3) K)
  rw [hadj, Matrix.trace_smul, htr', htr, hdet] at hCH
  simp only [smul_zero, zero_smul, sub_zero, add_zero, one_smul, sub_eq_zero] at hCH
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, hCH, Units.val_one])

theorem l3gl_conj_pow {X B : GL (Fin 3) K} {d : Kˣ} (h : X * B * X⁻¹ = B * S d) (j : ℕ) :
    X * B ^ j * X⁻¹ = B ^ j * S (d ^ j) := by
  have hc : Commute B (S d) := (Matrix.GeneralLinearGroup.scalar_commute d B).symm
  have h1 : (MulAut.conj X) (B ^ j) = (B * S d) ^ j := by
    rw [map_pow, MulAut.conj_apply, h]
  rw [MulAut.conj_apply] at h1
  rw [h1, hc.mul_pow, map_pow]

theorem l3gl_gdet_scalar (c : Kˣ) :
    Matrix.GeneralLinearGroup.det (S c : GL (Fin 3) K) = c ^ 3 :=
  Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, l3gl_det_scalar, Units.val_pow_eq_pow_val])

theorem l3gl_cube_eq_one_of_conj {X Y : GL (Fin 3) K} {d : Kˣ} (h : X * Y * X⁻¹ = Y * S d) :
    d ^ 3 = 1 := by
  have h1 := congrArg Matrix.GeneralLinearGroup.det h
  simp only [map_mul, map_inv, l3gl_gdet_scalar] at h1
  have h2 : Matrix.GeneralLinearGroup.det Y * d ^ 3 = Matrix.GeneralLinearGroup.det Y := by
    rw [← h1, mul_comm (Matrix.GeneralLinearGroup.det X), mul_assoc, mul_inv_cancel, mul_one]
  exact mul_eq_left.mp h2

theorem l3gl_cube_scalar {A B : GL (Fin 3) K} {c : Kˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hAB : A * B = B * A * S c) : ∃ a : Kˣ, A ^ 3 = S a := by
  have hW : HeisAux.W (A ^ 3) B (c ^ 3) := HeisAux.W_pow_left (HeisAux.WAB hAB) 3
  unfold HeisAux.W at hW
  rw [hc3, map_one, mul_one, mul_inv_eq_iff_eq_mul] at hW
  have hm : (A : Matrix (Fin 3) (Fin 3) K) * ((A ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((A ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_succ', ← pow_succ]
  have hm' : (B : Matrix (Fin 3) (Fin 3) K) *
      ((A ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((A ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B := by
    rw [← Units.val_mul, ← Units.val_mul, ← hW]
  obtain ⟨x, hx⟩ := HeisAux.commutant_scalar hc3 hc1 hAB hm hm'
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 := (A ^ 3 : GL (Fin 3) K).mul_inv
    rw [hx, h0, zero_smul, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
  rw [hx]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem l3gl_conj_scalar (g : GL (Fin 3) K) (d : Kˣ) : g * S d * g⁻¹ = S d := by
  rw [← Matrix.GeneralLinearGroup.scalar_commute d g]
  group

theorem l3gl_comm_aux (X Y : GL (Fin 3) K) (d m : Kˣ) :
    X * (Y * S d) * S m = S d * (X * Y * S m) := by
  have h1 := Matrix.GeneralLinearGroup.scalar_commute d X
  have h2 := Matrix.GeneralLinearGroup.scalar_commute d Y
  calc X * (Y * S d) * S m = X * (S d * Y) * S m := by rw [h2]
    _ = (X * S d) * Y * S m := by group
    _ = (S d * X) * Y * S m := by rw [h1]
    _ = _ := by group

theorem l3gl_comm_aux' (X Y : GL (Fin 3) K) (d m : Kˣ) :
    X * S d * Y * S m = S d * (X * Y * S m) := by
  have h1 := Matrix.GeneralLinearGroup.scalar_commute d X
  calc X * S d * Y * S m = (S d * X) * Y * S m := by rw [h1]
    _ = _ := by group

theorem l3gl_heis_cube {A B W : GL (Fin 3) K} {c dA dB : Kˣ} (hc1 : c ≠ 1)
    (hAB : A * B = B * A * S c) (hYA : W * A * W⁻¹ = A * S dA) (hYB : W * B * W⁻¹ = B * S dB)
    (hdet : (W : Matrix (Fin 3) (Fin 3) K).det = 1) : W ^ 3 = 1 := by
  have hABc : A * B * A⁻¹ = B * S c := by
    calc A * B * A⁻¹ = B * A * S c * A⁻¹ := by rw [hAB]
      _ = B * (A * S c) * A⁻¹ := by group
      _ = B * (S c * A) * A⁻¹ := by rw [Matrix.GeneralLinearGroup.scalar_commute c A]
      _ = B * S c := by group
  have hBA : B * A = A * B * S c⁻¹ := by
    rw [hAB, mul_assoc, ← map_mul]
    simp
  have hBAc : B * A * B⁻¹ = A * S c⁻¹ := by
    calc B * A * B⁻¹ = A * (B * S c⁻¹) * B⁻¹ := by rw [hBA]; group
      _ = A * (S c⁻¹ * B) * B⁻¹ := by rw [Matrix.GeneralLinearGroup.scalar_commute c⁻¹ B]
      _ = A * S c⁻¹ := by group
  have hc3 : c ^ 3 = 1 := l3gl_cube_eq_one_of_conj hABc
  obtain ⟨i, j, m, hW⟩ := heisenberg_normalizer hc3 hc1 hAB (l3gl_cube_eq_one_of_conj hYA)
    (l3gl_cube_eq_one_of_conj hYB) hYA hYB
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcne : ∀ n : ℕ, ¬ 3 ∣ n → c ^ n ≠ 1 := fun n hn h1 =>
    hn (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  by_cases hj : 3 ∣ j
  · by_cases hi : 3 ∣ i
    · obtain ⟨i', rfl⟩ := hi
      obtain ⟨j', rfl⟩ := hj
      obtain ⟨a, ha⟩ := l3gl_cube_scalar hc3 hc1 hAB
      obtain ⟨b, hb⟩ := l3gl_cube_scalar (A := B) (B := A) (c := c⁻¹) (by rw [inv_pow, hc3, inv_one])
        (inv_ne_one.2 hc1) (by rw [hBA])
      have hWs : W = S (a ^ i' * b ^ j' * m) := by
        rw [hW, pow_mul, pow_mul, ha, hb, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
      have hr : ((a ^ i' * b ^ j' * m : Kˣ) : K) ^ 3 = 1 := by
        rw [hWs, l3gl_det_scalar] at hdet
        exact hdet
      rw [hWs]
      exact l3gl_scalar_pow_three hr
    · have h : B * W * B⁻¹ = S ((c⁻¹) ^ i) * W := by
        rw [hW]
        calc B * (A ^ i * B ^ j * S m) * B⁻¹
            = (B * A ^ i * B⁻¹) * B ^ j * (S m) := by
              rw [show (B * (A ^ i * B ^ j * S m) * B⁻¹) =
                (B * A ^ i * B⁻¹) * B ^ j * (B * S m * B⁻¹) by group, l3gl_conj_scalar]
          _ = (A ^ i * S ((c⁻¹) ^ i)) * B ^ j * S m := by
              rw [l3gl_conj_pow hBAc i]
          _ = S ((c⁻¹) ^ i) * (A ^ i * B ^ j * S m) := l3gl_comm_aux' _ _ _ _
      refine l3gl_pow_three_eq_one ?_ h hdet
      rw [inv_pow]
      exact inv_ne_one.2 (hcne i hi)
  · have h : A * W * A⁻¹ = S (c ^ j) * W := by
      rw [hW]
      calc A * (A ^ i * B ^ j * S m) * A⁻¹
          = A ^ i * (A * B ^ j * A⁻¹) * (S m) := by
            rw [show (A * (A ^ i * B ^ j * S m) * A⁻¹) =
              A ^ i * (A * B ^ j * A⁻¹) * (A * S m * A⁻¹) by group, l3gl_conj_scalar]
        _ = A ^ i * (B ^ j * S (c ^ j)) * S m := by rw [l3gl_conj_pow hABc j]
        _ = S (c ^ j) * (A ^ i * B ^ j * S m) := l3gl_comm_aux _ _ _ _
    exact l3gl_pow_three_eq_one (hcne j hj) h hdet

end CFSG.HardMathSupport.Solomon.Coordinator
