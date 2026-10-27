module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313In

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof

open Matrix

section Poly

variable {K : Type*} [Field K] {R : Type*} [Ring R] [Algebra K R]

@[expose] def cp (Y : R) (a b c : K) : R := a • (Y * Y) + b • Y + c • 1

theorem cp_mul_cp {Y : R} (hY : Y * Y * Y = 1) (a b c a' b' c' : K) :
    cp Y a b c * cp Y a' b' c' =
      cp Y (a * c' + b * b' + c * a') (a * a' + b * c' + c * b') (a * b' + b * a' + c * c') := by
  have h4 : Y * Y * (Y * Y) = Y := by rw [← mul_assoc, hY, one_mul]
  have h3 : Y * (Y * Y) = 1 := by rw [← mul_assoc, hY]
  simp only [cp, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, h4, h3, hY, add_smul]
  abel

theorem cp_one_eq (Y : R) : (1 : R) = cp Y (0 : K) 0 1 := by
  simp [cp]

theorem cp_zero_eq (Y : R) : (0 : R) = cp Y (0 : K) 0 0 := by
  simp [cp]

theorem cp_add_cp (Y : R) (a b c a' b' c' : K) :
    cp Y a b c + cp Y a' b' c' = cp Y (a + a') (b + b') (c + c') := by
  simp only [cp, add_smul]
  abel

theorem commute_cp {Y e : R} (he : e * Y = Y * e) (a b c : K) : e * cp Y a b c = cp Y a b c * e := by
  have he2 : e * (Y * Y) = Y * Y * e := by
    rw [← mul_assoc, he, mul_assoc, he, mul_assoc]
  simp only [cp, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, he2, he, one_mul, mul_one]

theorem mul_cp_of_comm {X Y : R} {κ : K} (hXY : X * Y = κ • (Y * X)) (a b c : K) :
    X * cp Y a b c = cp Y (a * κ ^ 2) (b * κ) c * X := by
  have h2 : X * (Y * Y) = (κ ^ 2) • (Y * Y * X) := by
    rw [← mul_assoc, hXY, smul_mul_assoc, mul_assoc, hXY, mul_smul_comm, smul_smul, sq,
      ← mul_assoc]
  simp only [cp, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h2, hXY, smul_smul, mul_one,
    one_mul]

end Poly

section Heis

variable {K : Type*} [Field K] {R : Type*} [Ring R] [Algebra K R]

@[expose] def heisInv (X Xi Y : R) (κ : K) : R :=
  X * cp Y (1 : K) 1 1 + Xi * cp Y (κ ^ 2) κ 1 + cp Y κ (κ ^ 2) 1

theorem cube_eq_one_of_sq_add {κ : K} (hκ : κ ^ 2 + κ + 1 = 0) : κ ^ 3 = 1 := by
  linear_combination (κ - 1) * hκ

theorem inv_mul_of_comm {X Xi Y : R} {κ : K} (hκ : κ ^ 2 + κ + 1 = 0) (hXY : X * Y = κ • (Y * X))
    (hXXi : X * Xi = 1) (hXiX : Xi * X = 1) : Xi * Y = (κ ^ 2) • (Y * Xi) := by
  have h3 := cube_eq_one_of_sq_add hκ
  have e1 : Y * Xi = κ • (Xi * Y) := by
    calc Y * Xi = Xi * (X * Y) * Xi := by
          rw [← mul_assoc, hXiX, one_mul]
      _ = κ • (Xi * Y) := by
          rw [hXY, mul_smul_comm, smul_mul_assoc, mul_assoc, mul_assoc, hXXi, mul_one]
  rw [e1, smul_smul, ← pow_succ, h3, one_smul]

variable {X Xi Y : R} {κ : K} (h2 : (2 : K) = 0) (hκ : κ ^ 2 + κ + 1 = 0) (hY : Y * Y * Y = 1)
  (hXY : X * Y = κ • (Y * X)) (hXXi : X * Xi = 1) (hXiX : Xi * X = 1)

include h2 hκ hY in
theorem heis_proj :
    cp Y (1 : K) 1 1 * cp Y (1 : K) 1 1 = cp Y (1 : K) 1 1 ∧
    cp Y κ (κ ^ 2) 1 * cp Y κ (κ ^ 2) 1 = cp Y κ (κ ^ 2) 1 ∧
    cp Y (κ ^ 2) κ 1 * cp Y (κ ^ 2) κ 1 = cp Y (κ ^ 2) κ 1 ∧
    cp Y (1 : K) 1 1 * cp Y κ (κ ^ 2) 1 = 0 ∧ cp Y κ (κ ^ 2) 1 * cp Y (1 : K) 1 1 = 0 ∧
    cp Y (1 : K) 1 1 * cp Y (κ ^ 2) κ 1 = 0 ∧ cp Y (κ ^ 2) κ 1 * cp Y (1 : K) 1 1 = 0 ∧
    cp Y κ (κ ^ 2) 1 * cp Y (κ ^ 2) κ 1 = 0 ∧ cp Y (κ ^ 2) κ 1 * cp Y κ (κ ^ 2) 1 = 0 ∧
    cp Y (1 : K) 1 1 + cp Y κ (κ ^ 2) 1 + cp Y (κ ^ 2) κ 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cp_mul_cp hY]; congr 1 <;> grind
  · rw [cp_mul_cp hY]; congr 1 <;> grind
  · rw [cp_mul_cp hY]; congr 1 <;> grind
  · rw [cp_mul_cp hY, cp_zero_eq (K := K) Y]; congr 1 <;> grind
  · rw [cp_mul_cp hY, cp_zero_eq (K := K) Y]; congr 1 <;> grind
  · rw [cp_mul_cp hY, cp_zero_eq (K := K) Y]; congr 1 <;> grind
  · rw [cp_mul_cp hY, cp_zero_eq (K := K) Y]; congr 1 <;> grind
  · rw [cp_mul_cp hY, cp_zero_eq (K := K) Y]; congr 1 <;> grind
  · rw [cp_mul_cp hY, cp_zero_eq (K := K) Y]; congr 1 <;> grind
  · rw [cp_add_cp, cp_add_cp, cp_one_eq (K := K) Y]; congr 1 <;> grind

include hκ hXY in
theorem heis_X_p1 : X * cp Y (1 : K) 1 1 = cp Y (κ ^ 2) κ 1 * X := by
  rw [mul_cp_of_comm hXY, one_mul, one_mul]

include hκ hXY in
theorem heis_X_pc : X * cp Y κ (κ ^ 2) 1 = cp Y (1 : K) 1 1 * X := by
  have h3 := cube_eq_one_of_sq_add hκ
  rw [mul_cp_of_comm hXY, ← pow_succ', h3, ← pow_succ, h3]

include hκ hXY hXXi hXiX in
theorem heis_Xi_p2 : Xi * cp Y (κ ^ 2) κ 1 = cp Y (1 : K) 1 1 * Xi := by
  have h3 := cube_eq_one_of_sq_add hκ
  have e1 : κ ^ 2 * (κ ^ 2) ^ 2 = 1 := by
    have : κ ^ 2 * (κ ^ 2) ^ 2 = (κ ^ 3) ^ 2 := by ring
    rw [this, h3, one_pow]
  have e2 : κ * κ ^ 2 = 1 := by rw [← pow_succ', h3]
  rw [mul_cp_of_comm (inv_mul_of_comm hκ hXY hXXi hXiX), e1, e2]

include h2 hκ hY hXY hXXi hXiX in
theorem heisInv_mul_self : heisInv X Xi Y κ * heisInv X Xi Y κ = 1 := by
  obtain ⟨p11, pcc, p22, p1c, pc1, p12, p21, pc2, p2c, psum⟩ := heis_proj (Y := Y) h2 hκ hY
  have hA := heis_X_p1 (X := X) hκ hXY
  have hB := heis_Xi_p2 hκ hXY hXXi hXiX
  set p1 := cp Y (1 : K) 1 1
  set pc := cp Y κ (κ ^ 2) 1
  set q := cp Y (κ ^ 2) κ 1
  have hτ : heisInv X Xi Y κ = q * X + p1 * Xi + pc := by
    rw [heisInv, hA, hB]
  calc heisInv X Xi Y κ * heisInv X Xi Y κ = (X * p1 + Xi * q + pc) * (q * X + p1 * Xi + pc) := by
        rw [← hτ]; rfl
    _ = X * (p1 * q) * X + X * (p1 * p1) * Xi + X * (p1 * pc) + Xi * (q * q) * X +
        Xi * (q * p1) * Xi + Xi * (q * pc) + pc * q * X + pc * p1 * Xi + pc * pc := by
        simp only [add_mul, mul_add, mul_assoc]
        abel
    _ = q * (X * Xi) + p1 * (Xi * X) + pc := by
        rw [p12, p11, p1c, p22, p21, p2c, pc2, pc1, pcc]
        simp only [mul_zero, zero_mul, add_zero, zero_add]
        rw [hA, hB, mul_assoc, mul_assoc]
    _ = 1 := by
        rw [hXXi, hXiX, mul_one, mul_one, ← psum]
        abel

include hY in
theorem commute_heisInv {e : R} (heX : e * X = X * e) (heXi : e * Xi = Xi * e)
    (heY : e * Y = Y * e) : e * heisInv X Xi Y κ = heisInv X Xi Y κ * e := by
  have h1 : ∀ (Z : R) (a b c : K), e * Z = Z * e → e * (Z * cp Y a b c) = Z * cp Y a b c * e := by
    intro Z a b c hZ
    rw [← mul_assoc, hZ, mul_assoc, commute_cp heY, ← mul_assoc]
  simp only [heisInv, mul_add, add_mul]
  rw [h1 X _ _ _ heX, h1 Xi _ _ _ heXi, commute_cp heY]

include h2 hκ hY hXY hXXi hXiX in
theorem heisInv_ne_smul [Nontrivial R] (d : K) : heisInv X Xi Y κ ≠ d • 1 := by
  intro hd
  obtain ⟨p11, pcc, p22, p1c, pc1, p12, p21, pc2, p2c, psum⟩ := heis_proj (Y := Y) h2 hκ hY
  have hA := heis_X_p1 (X := X) hκ hXY
  have hC := heis_X_pc (X := X) hκ hXY
  have h1 : heisInv X Xi Y κ * cp Y (1 : K) 1 1 = X * cp Y (1 : K) 1 1 := by
    simp only [heisInv, add_mul, mul_assoc, p11, p21, pc1, mul_zero, add_zero]
  set p1 := cp Y (1 : K) 1 1
  set pc := cp Y κ (κ ^ 2) 1
  set q := cp Y (κ ^ 2) κ 1
  rw [hd, smul_mul_assoc, one_mul, hA] at h1
  have hq0 : q * X = 0 := by
    have := congrArg (fun z => q * z) h1
    simp only [mul_smul_comm, p21, smul_zero] at this
    rw [← mul_assoc, p22] at this
    exact this.symm
  have hq : q = 0 := by rw [← mul_one q, ← hXXi, ← mul_assoc, hq0, zero_mul]
  have hp1 : p1 = 0 := by
    rw [← one_mul p1, ← hXiX, mul_assoc, hA, hq, zero_mul, mul_zero]
  have hpc : pc = 0 := by
    rw [← one_mul pc, ← hXiX, mul_assoc, hC, hp1, zero_mul, mul_zero]
  apply one_ne_zero (α := R)
  rw [← psum, hp1, hpc, hq, add_zero, add_zero]

end Heis

section Scalars

variable {K : Type} [Field K] {n : ℕ}

theorem coe_scalar_mul (c : Kˣ) (g : GL (Fin n) K) :
    ((GeneralLinearGroup.scalar (Fin n) c * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) • (g : Matrix (Fin n) (Fin n) K) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_eq_diagonal_mul]

theorem scalar_injective (hn : 1 ≤ n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
  intro c d hcd
  have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hcd
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

theorem mul_cube_of_comm {R : Type*} [Ring R] [Algebra K R] {X Y : R} {κ : K}
    (hXY : X * Y = κ • (Y * X)) : X * (Y * Y * Y) = κ ^ 3 • (Y * Y * Y * X) := by
  have e2 : X * (Y * Y) = κ ^ 2 • (Y * Y * X) := by
    rw [← mul_assoc, hXY, smul_mul_assoc, mul_assoc, hXY, mul_smul_comm, smul_smul, sq,
      ← mul_assoc]
  rw [← mul_assoc, e2, smul_mul_assoc, mul_assoc (Y * Y) X Y, hXY, mul_smul_comm, smul_smul,
    ← pow_succ, ← mul_assoc]

theorem cube_eq_one_of_comm (hn : 1 ≤ n) {g z : GL (Fin n) K} {c : K}
    (hgz : (g : Matrix (Fin n) (Fin n) K) * z = c • ((z : Matrix (Fin n) (Fin n) K) * g))
    (hz3 : ∃ d : Kˣ, z ^ 3 = GeneralLinearGroup.scalar (Fin n) d) : c ^ 3 = 1 := by
  obtain ⟨d, hd⟩ := hz3
  have e1 := mul_cube_of_comm hgz
  have hz : (z : Matrix (Fin n) (Fin n) K) * z * z = (d : K) • 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_three', hd, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, smul_one_eq_diagonal]
  rw [hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul] at e1
  have e2 := congrArg (fun M => M * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) e1
  simp only [Matrix.smul_mul] at e2
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at e2
  have e3 := congrFun (congrFun e2 ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e3
  have hd0 : (d : K) ≠ 0 := d.ne_zero
  have : (d : K) * (c ^ 3 - 1) = 0 := by linear_combination -e3
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hd0)

theorem cube_mul_of_comm (hn : 1 ≤ n) {g g' : GL (Fin n) K} {c : Kˣ}
    (hgg : g * g' = GeneralLinearGroup.scalar (Fin n) c * (g' * g))
    (hg3 : ∃ d : Kˣ, g' ^ 3 = GeneralLinearGroup.scalar (Fin n) d) :
    (g * g') ^ 3 = g ^ 3 * g' ^ 3 := by
  have hgg' : (g : Matrix (Fin n) (Fin n) K) * g' = (c : K) • ((g' : Matrix (Fin n) (Fin n) K) * g) := by
    rw [← Units.val_mul, hgg, coe_scalar_mul, Units.val_mul]
  have hc3 := cube_eq_one_of_comm hn hgg' hg3
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  apply Units.ext
  set A : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K)
  set B : Matrix (Fin n) (Fin n) K := (g' : Matrix (Fin n) (Fin n) K)
  have hba : B * A = (c : K)⁻¹ • (A * B) := by
    rw [hgg', smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hci : ((c : K)⁻¹) ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    pow_three', pow_three', pow_three', Units.val_mul]
  change A * B * (A * B) * (A * B) = A * A * A * (B * B * B)
  calc A * B * (A * B) * (A * B) = A * (B * A) * (B * A) * B := by
        simp only [Matrix.mul_assoc]
    _ = ((c : K)⁻¹ * (c : K)⁻¹) • (A * A * (B * A) * B * B) := by
        conv_lhs => rw [hba]
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
    _ = ((c : K)⁻¹ ^ 3) • (A * A * A * (B * B * B)) := by
        conv_lhs => rw [hba]
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
        congr 1
        ring
    _ = A * A * A * (B * B * B) := by rw [hci, one_smul]

end Scalars

section Mat

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

@[expose] noncomputable def ct (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := (M.map h.bar)ᵀ

theorem ct_mul (M N : Matrix (Fin n) (Fin n) K) : ct h (M * N) = ct h N * ct h M := by
  rw [ct, ct, ct, Matrix.map_mul, transpose_mul]

theorem ct_add (M N : Matrix (Fin n) (Fin n) K) : ct h (M + N) = ct h M + ct h N := by
  rw [ct, ct, ct, Matrix.map_add _ (map_add h.bar), transpose_add]

theorem ct_smul (a : K) (M : Matrix (Fin n) (Fin n) K) : ct h (a • M) = h.bar a • ct h M := by
  ext i j
  simp [ct]

theorem ct_one : ct h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [ct, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

theorem ct_cp {Y : Matrix (Fin n) (Fin n) K} (hY : Y * Y * Y = 1) (hYct : ct h Y = Y * Y)
    (a b c : K) : ct h (cp Y a b c) = cp Y (h.bar b) (h.bar a) (h.bar c) := by
  have h4 : Y * Y * (Y * Y) = Y := by rw [← mul_assoc, hY, one_mul]
  simp only [cp, ct_add, ct_smul, ct_mul, hYct, h4, ct_one]
  abel

theorem ct_mul_self_of_mem {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ct h (A : Matrix (Fin n) (Fin n) K) * A = 1 := by
  have := mem_primeFormUnitary.mp hA
  rw [Units.val_one, Matrix.mul_one] at this
  exact this

theorem ct_eq_inv_of_mem {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ct h (A : Matrix (Fin n) (Fin n) K) = ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  calc ct h (A : Matrix (Fin n) (Fin n) K) =
        ct h (A : Matrix (Fin n) (Fin n) K) * ((A : Matrix (Fin n) (Fin n) K) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, ct_mul_self_of_mem h hA, Matrix.one_mul]

theorem bar_eq_sq_of_cube {κ : K} (hq3 : 3 ∣ p ^ f + 1) (hκ3 : κ ^ 3 = 1) : h.bar κ = κ ^ 2 := by
  rw [UnitaryFieldData.bar_apply]
  have hmod : p ^ f % 3 = 2 := by omega
  rw [← Nat.div_add_mod (p ^ f) 3, hmod, pow_add, pow_mul, hκ3, one_pow, one_mul]

theorem exists_heis_involution [CharP K 2] (hq3 : 3 ∣ p ^ f + 1) (hn : 1 ≤ n)
    {x y : GL (Fin n) K}
    (hx : x ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hy : y ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hy3 : y ^ 3 = 1) {κ : K}
    (hxy : (x : Matrix (Fin n) (Fin n) K) * y = κ • ((y : Matrix (Fin n) (Fin n) K) * x))
    (hκ1 : κ ≠ 1) :
    ∃ t ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), t ^ 2 = 1 ∧
      (∀ c : Kˣ, t ≠ GeneralLinearGroup.scalar (Fin n) c) ∧
      ∀ e : GL (Fin n) K, e * x = x * e → e * y = y * e → e * t = t * e := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set X : Matrix (Fin n) (Fin n) K := (x : Matrix (Fin n) (Fin n) K) with hXdef
  set Xi : Matrix (Fin n) (Fin n) K := ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXidef
  set Y : Matrix (Fin n) (Fin n) K := (y : Matrix (Fin n) (Fin n) K) with hYdef
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hXXi : X * Xi = 1 := by rw [hXdef, hXidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXiX : Xi * X = 1 := by rw [hXdef, hXidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hY : Y * Y * Y = 1 := by
    rw [hYdef, ← Units.val_mul, ← Units.val_mul, ← pow_three', hy3, Units.val_one]
  have hκ3 : κ ^ 3 = 1 := cube_eq_one_of_comm hn hxy ⟨1, by rw [hy3, map_one]⟩
  have hκ : κ ^ 2 + κ + 1 = 0 := by
    have : (κ - 1) * (κ ^ 2 + κ + 1) = 0 := by linear_combination hκ3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hκ1)
  have hbκ : h.bar κ = κ ^ 2 := bar_eq_sq_of_cube h hq3 hκ3
  have hbκ2 : h.bar (κ ^ 2) = κ := by
    rw [map_pow, hbκ, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hκ3, one_mul]
  have hb1 : h.bar 1 = 1 := map_one h.bar
  have hYct : ct h Y = Y * Y := by
    have hu : ct h Y * Y = 1 := ct_mul_self_of_mem h hy
    calc ct h Y = ct h Y * (Y * Y * Y) := by rw [hY, Matrix.mul_one]
      _ = Y * Y := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hXct : ct h X = Xi := ct_eq_inv_of_mem h hx
  have hXict : ct h Xi = X := by
    have := ct_eq_inv_of_mem h (inv_mem hx)
    rw [inv_inv] at this
    exact this
  have hA := heis_X_p1 (X := X) hκ hxy
  have hB := heis_Xi_p2 hκ hxy hXXi hXiX
  set τ := heisInv X Xi Y κ with hτdef
  have hττ : τ * τ = 1 := heisInv_mul_self h2 hκ hY hxy hXXi hXiX
  have hτct : ct h τ = τ := by
    rw [hτdef, heisInv, ct_add, ct_add, ct_mul, ct_mul, hXct, hXict, ct_cp h hY hYct,
      ct_cp h hY hYct, ct_cp h hY hYct, hb1, hbκ, hbκ2, hA, hB]
    abel
  let t : GL (Fin n) K := ⟨τ, τ, hττ, hττ⟩
  have htU : t ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    change ct h τ * τ = 1
    rw [hτct, hττ]
  have hdet : (τ : Matrix (Fin n) (Fin n) K).det = 1 := by
    have e1 : τ.det * τ.det = 1 := by rw [← Matrix.det_mul, hττ, Matrix.det_one]
    have e2 : (τ.det - 1) * (τ.det - 1) = 0 := by linear_combination e1 - τ.det * h2 + h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp e2)
  refine ⟨t, (mem_gramSU_iff_unitary h).mpr ⟨htU, hdet⟩, ?_, fun c hc => ?_, fun e hex hey => ?_⟩
  · rw [sq]
    exact Units.ext hττ
  · have hc' : τ = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
      simp only [GeneralLinearGroup.coe_scalar] at this
      rw [smul_one_eq_diagonal]
      exact this
    exact heisInv_ne_smul h2 hκ hY hxy hXXi hXiX (c : K) hc'
  · apply Units.ext
    change (e : Matrix (Fin n) (Fin n) K) * τ = τ * e
    have heX : (e : Matrix (Fin n) (Fin n) K) * X = X * e := by
      rw [hXdef, ← Units.val_mul, hex, Units.val_mul]
    have heXi : (e : Matrix (Fin n) (Fin n) K) * Xi = Xi * e := by
      have : e * x⁻¹ = x⁻¹ * e := (show Commute e x from hex).inv_right
      rw [hXidef, ← Units.val_mul, this, Units.val_mul]
    have heY : (e : Matrix (Fin n) (Fin n) K) * Y = Y * e := by
      rw [hYdef, ← Units.val_mul, hey, Units.val_mul]
    exact commute_heisInv hY heX heXi heY

end Mat

section Swap

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem diag_mul_swap_comm {D : Matrix (Fin n) (Fin n) K} (hD : D.IsDiag) {i₀ i₁ : Fin n}
    (h01 : D i₀ i₀ = D i₁ i₁) :
    D * (Equiv.swap i₀ i₁).permMatrix K = (Equiv.swap i₀ i₁).permMatrix K * D := by
  rw [← hD.diagonal_diag]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, CFSG.RankThree.Classical.permMatrix_apply']
  split_ifs with hab
  · rw [mul_one, one_mul, ← hab]
    simp only [Matrix.diag_apply]
    rcases eq_or_ne a i₀ with rfl | ha0
    · rw [Equiv.swap_apply_left]
      exact h01
    · rcases eq_or_ne a i₁ with rfl | ha1
      · rw [Equiv.swap_apply_right]
        exact h01.symm
      · rw [Equiv.swap_apply_of_ne_of_ne ha0 ha1]
  · rw [mul_zero, zero_mul]

theorem exists_swap_involution [CharP K 2] (hn : 2 ≤ n) (W : GL (Fin n) K)
    (hW : W ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ t ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), t ^ 2 = 1 ∧
      (∀ c : Kˣ, t ≠ GeneralLinearGroup.scalar (Fin n) c) ∧
      ∀ e : GL (Fin n) K, ((W⁻¹ * e * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag →
        ((W⁻¹ * e * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩ =
          ((W⁻¹ * e * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨1, by omega⟩ ⟨1, by omega⟩ →
        e * t = t * e := by
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := by
    intro he
    have := congrArg Fin.val he
    simp [hi₀, hi₁] at this
  set s : GL (Fin n) K := CFSG.RankThree.Classical.unitaryPermGL (Equiv.swap i₀ i₁) with hsdef
  have hmap : ((Equiv.swap i₀ i₁).permMatrix K).map h.bar = (Equiv.swap i₀ i₁).permMatrix K :=
    Matrix.ext fun a b => by
      rw [Matrix.map_apply, CFSG.RankThree.Classical.permMatrix_apply']
      split_ifs <;> simp
  have hs : s ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    refine mem_gramSU.2 ⟨?_, ?_⟩
    · rw [Units.val_one, Matrix.mul_one, hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL, hmap,
        Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
        Matrix.permMatrix_one]
    · rw [hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL, Matrix.det_permutation,
        Equiv.Perm.sign_swap h01, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      exact CharTwo.neg_eq 1
  have hs2 : s * s = 1 := Units.ext (by
    rw [Units.val_mul, hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL, ← Matrix.permMatrix_mul,
      Equiv.swap_mul_self, Matrix.permMatrix_one, Units.val_one])
  refine ⟨W * s * W⁻¹, conj_mem_gramSU h _ hW hs, ?_, ?_, ?_⟩
  · rw [sq]
    calc W * s * W⁻¹ * (W * s * W⁻¹) = W * (s * s) * W⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  · intro c hc
    have hsc : s = GeneralLinearGroup.scalar (Fin n) c := by
      have e1 : s = W⁻¹ * (W * s * W⁻¹) * W := by group
      rw [e1, hc, (commute_scalar c W⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
    have e2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i₁ i₀) hsc
    simp only [hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL,
      CFSG.RankThree.Classical.permMatrix_apply', Equiv.swap_apply_right, if_true,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h01.symm] at e2
    exact one_ne_zero e2
  · intro e hD hd
    have hDs : (W⁻¹ * e * W) * s = s * (W⁻¹ * e * W) := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hsdef, CFSG.RankThree.Classical.coe_unitaryPermGL]
      exact diag_mul_swap_comm hD hd)
    calc e * (W * s * W⁻¹) = W * ((W⁻¹ * e * W) * s) * W⁻¹ := by group
      _ = W * (s * (W⁻¹ * e * W)) * W⁻¹ := by rw [hDs]
      _ = W * s * W⁻¹ * e := by group

end Swap

section Local

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem exists_centralized_involution [CharP K 2] (hq3 : 3 ∣ p ^ f + 1) (hn : 2 ≤ n)
    (P : Subgroup (GL (Fin n) K))
    (hPU : P ≤ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hZ : ∀ c : Kˣ, h.norm (c : K) = 1 → GeneralLinearGroup.scalar (Fin n) c ∈ P)
    (hcube : ∀ g ∈ P, ∃ c : Kˣ, g ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hcomm : ∀ g ∈ P, ∀ g' ∈ P, ∃ c : Kˣ,
      g * g' = GeneralLinearGroup.scalar (Fin n) c * (g' * g)) :
    ∃ E : Subgroup (GL (Fin n) K), E ≤ P ∧ Nat.card P ≤ 9 * Nat.card E ∧
      ∃ t ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), t ^ 2 = 1 ∧
        (∀ c : Kˣ, t ≠ GeneralLinearGroup.scalar (Fin n) c) ∧ ∀ e ∈ E, e * t = t * e := by
  classical
  have hn1 : 1 ≤ n := by omega
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (GL (Fin n) K) := inferInstance
  have hconj : ∀ g ∈ P, ∀ z ∈ P, ∃ ζ : rootsOfUnity 3 K,
      g * z * g⁻¹ = GeneralLinearGroup.scalar (Fin n) (ζ : Kˣ) * z := by
    intro g hg z hz
    obtain ⟨c, hc⟩ := hcomm g hg z hz
    have hc' : (g : Matrix (Fin n) (Fin n) K) * z =
        (c : K) • ((z : Matrix (Fin n) (Fin n) K) * g) := by
      rw [← Units.val_mul, hc, coe_scalar_mul, Units.val_mul]
    have hc3 : (c : K) ^ 3 = 1 := cube_eq_one_of_comm hn1 hc' (hcube z hz)
    refine ⟨⟨c, (mem_rootsOfUnity 3 c).2
      (Units.ext (by rw [Units.val_pow_eq_pow_val, hc3, Units.val_one]))⟩, ?_⟩
    rw [hc, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  let T : GL (Fin n) K → Finset (GL (Fin n) K) := fun z =>
    Finset.univ.image fun ζ : rootsOfUnity 3 K => GeneralLinearGroup.scalar (Fin n) (ζ : Kˣ) * z
  have hT : ∀ z, (T z).card ≤ 3 := fun z => by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact card_rootsOfUnity K 3
  have hidx : ∀ z ∈ P, (Subgroup.centralizer ({z} : Set (GL (Fin n) K))).relIndex P ≤ 3 := by
    intro z hz
    refine (relIndex_centralizer_le P z (T z) fun g hg => ?_).trans (hT z)
    obtain ⟨ζ, hζ⟩ := hconj g hg z hz
    exact Finset.mem_image.2 ⟨ζ, Finset.mem_univ _, hζ.symm⟩
  by_cases hc3 : ∃ y ∈ P, y ^ 3 = 1 ∧ ∃ x ∈ P, x * y ≠ y * x
  ·
    obtain ⟨y, hyP, hy3, x, hxP, hxy⟩ := hc3
    obtain ⟨c, hc⟩ := hcomm x hxP y hyP
    have hc' : (x : Matrix (Fin n) (Fin n) K) * y =
        (c : K) • ((y : Matrix (Fin n) (Fin n) K) * x) := by
      rw [← Units.val_mul, hc, coe_scalar_mul, Units.val_mul]
    have hc1 : (c : K) ≠ 1 := by
      intro h1
      apply hxy
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hc', h1, one_smul]
    obtain ⟨t, htSU, ht2, htns, htc⟩ :=
      exists_heis_involution h hq3 hn1 (hPU hxP) (hPU hyP) hy3 hc' hc1
    set Cx := Subgroup.centralizer ({x} : Set (GL (Fin n) K))
    set Cy := Subgroup.centralizer ({y} : Set (GL (Fin n) K))
    refine ⟨Cy ⊓ Cx ⊓ P, inf_le_right, ?_, t, htSU, ht2, htns, fun e he => ?_⟩
    · have h4 := Subgroup.relIndex_mul_card (Cy ⊓ Cx ⊓ P) P
      rw [inf_of_le_left (inf_le_right : Cy ⊓ Cx ⊓ P ≤ P), Subgroup.inf_relIndex_right] at h4
      rw [← h4]
      exact Nat.mul_le_mul_right _
        (Subgroup.relIndex_inf_le.trans (Nat.mul_le_mul (hidx y hyP) (hidx x hxP)))
    · exact htc e (Subgroup.mem_centralizer_singleton_iff.1 he.1.2)
        (Subgroup.mem_centralizer_singleton_iff.1 he.1.1)
  · push Not at hc3
    set U := primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hUdef
    let A₁ : Subgroup ↥U :=
      { carrier := {a | (a : GL (Fin n) K) ∈ P ∧ (a : GL (Fin n) K) ^ 3 = 1}
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          rw [Subgroup.coe_mul,
            (show Commute (a : GL (Fin n) K) b from hc3 _ hb.1 hb.2 _ ha.1).mul_pow, ha.2, hb.2,
            one_mul]⟩
        one_mem' := ⟨one_mem _, one_pow 3⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [Subgroup.coe_inv, inv_pow, ha.2, inv_one]⟩ }
    have hA₁comm : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb =>
      Subtype.ext (hc3 _ hb.1 hb.2 _ ha.1)
    have hA₁pow : ∀ a ∈ A₁, a ^ 3 = 1 := fun a ha =>
      Subtype.ext (by rw [Subgroup.coe_pow, ha.2, Subgroup.coe_one])
    obtain ⟨W₀, hW₀⟩ :=
      CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three hq3 A₁ hA₁comm hA₁pow
    set W : GL (Fin n) K := (W₀ : GL (Fin n) K) with hWdef
    obtain ⟨t, htSU, ht2, htns, htc⟩ := exists_swap_involution h hn W W₀.2
    have hcs : ∀ g : ↥P, ∃ c : Kˣ, (g : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c :=
      fun g => hcube g g.2
    have hmul3 : ∀ g ∈ P, ∀ g' ∈ P, (g * g') ^ 3 = g ^ 3 * g' ^ 3 := fun g hg g' hg' => by
      obtain ⟨c, hc⟩ := hcomm g hg g' hg'
      exact cube_mul_of_comm hn1 hc (hcube g' hg')
    let ψ : ↥P →* Kˣ :=
      { toFun := fun g => (hcs g).choose
        map_one' := scalar_injective hn1 (by
          rw [← (hcs 1).choose_spec, Subgroup.coe_one, one_pow, map_one])
        map_mul' := fun g g' => scalar_injective hn1 (by
          rw [map_mul, ← (hcs g).choose_spec, ← (hcs g').choose_spec, ← (hcs (g * g')).choose_spec,
            Subgroup.coe_mul, hmul3 g g.2 g' g'.2]) }
    have hψ : ∀ g : ↥P, (g : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (ψ g) :=
      fun g => (hcs g).choose_spec
    have hψN : ∀ g : ↥P, ψ g ∈ rootsOfUnity (p ^ f + 1) K := fun g => by
      have hmem : GeneralLinearGroup.scalar (Fin n) (ψ g) ∈ U := by
        rw [← hψ g]
        exact pow_mem (hPU g.2) 3
      have hN := norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 1 hmem
      rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
        ← h.norm_eq_pow]
      exact hN
    let ψ' : ↥P →* ↥(rootsOfUnity (p ^ f + 1) K) := ψ.codRestrict _ hψN
    set C3 := (powMonoidHom 3 : ↥(rootsOfUnity (p ^ f + 1) K) →*
      ↥(rootsOfUnity (p ^ f + 1) K)).range with hC3
    set P₁ : Subgroup ↥P := C3.comap ψ' with hP₁
    have hP₁idx : P₁.index ≤ 3 := by
      rw [hP₁, Subgroup.index_comap]
      have hdvd : C3.relIndex ψ'.range ∣ C3.index := Subgroup.relIndex_dvd_index_of_normal _ _
      have hidx3 : C3.index = (Nat.card ↥(rootsOfUnity (p ^ f + 1) K)).gcd 3 :=
        IsCyclic.index_powMonoidHom_range _ 3
      have hpos : 0 < C3.index := by
        rw [hidx3]
        exact Nat.gcd_pos_of_pos_right _ (by norm_num)
      exact (Nat.le_of_dvd hpos hdvd).trans (hidx3 ▸ Nat.gcd_le_right _ (by norm_num))
    set D : ↥P → Matrix (Fin n) (Fin n) K := fun g =>
      ((W⁻¹ * (g : GL (Fin n) K) * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDdef
    have hdiag : ∀ g : ↥P, g ∈ P₁ → (D g).IsDiag := by
      intro g hg
      obtain ⟨d, hd⟩ := hg
      have hd' : ((d : Kˣ)) ^ 3 = ψ g := by
        have := congrArg Subtype.val hd
        simpa [ψ'] using this
      have hdN : h.norm ((d : Kˣ) : K) = 1 := by
        have h1 := d.2
        rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
          ← h.norm_eq_pow] at h1
        exact h1
      have hdinvN : h.norm (((d : Kˣ)⁻¹ : Kˣ) : K) = 1 := by
        rw [Units.val_inv_eq_inv_val, CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq h, hdN, inv_one]
      obtain ⟨a, ha⟩ : ∃ a : GL (Fin n) K, a = GeneralLinearGroup.scalar (Fin n) (d : Kˣ)⁻¹ * g :=
        ⟨_, rfl⟩
      have haP : a ∈ P := by rw [ha]; exact mul_mem (hZ _ hdinvN) g.2
      have ha3 : a ^ 3 = 1 := by
        rw [ha, ((commute_scalar ((d : Kˣ)⁻¹) (g : GL (Fin n) K)).symm).mul_pow, hψ g, ← map_pow,
          ← map_mul, inv_pow, hd', inv_mul_cancel, map_one]
      have haA : (⟨a, hPU haP⟩ : ↥U) ∈ A₁ := ⟨haP, ha3⟩
      have hDa := hW₀ _ haA
      have hga : (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) (d : Kˣ) * a := by
        rw [ha, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      have hconjga : W⁻¹ * (g : GL (Fin n) K) * W =
          GeneralLinearGroup.scalar (Fin n) (d : Kˣ) * (W⁻¹ * a * W) := by
        rw [hga, ← mul_assoc W⁻¹, (commute_scalar (d : Kˣ) W⁻¹).eq]
        simp only [mul_assoc]
      have hDg : D g = ((d : Kˣ) : K) •
          ((W⁻¹ * a * W : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [hDdef]
        rw [hconjga, coe_scalar_mul]
      rw [hDg]
      exact hDa.smul _
    have hDmul : ∀ g g' : ↥P, D (g * g') = D g * D g' := fun g g' => by
      simp only [hDdef]
      rw [← Units.val_mul]
      congr 1
      simp only [Subgroup.coe_mul]
      group
    have hDne : ∀ g : ↥P, g ∈ P₁ → ∀ i, D g i i ≠ 0 := by
      intro g hg i hi
      have hdet : (D g).det ≠ 0 := (Matrix.isUnits_det_units _).ne_zero
      rw [← (hdiag g hg).diagonal_diag, Matrix.det_diagonal] at hdet
      exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hDentry : ∀ g g' : ↥P, g ∈ P₁ → ∀ i, D (g * g') i i = D g i i * D g' i i := by
      intro g g' hg i
      rw [hDmul]
      calc (D g * D g') i i = (Matrix.diagonal (Matrix.diag (D g)) * D g') i i := by
            rw [(hdiag g hg).diagonal_diag]
        _ = D g i i * D g' i i := by rw [Matrix.diagonal_mul]; rfl
    set i₀ : Fin n := ⟨0, by omega⟩
    set i₁ : Fin n := ⟨1, by omega⟩
    let χ : ↥P₁ →* Kˣ :=
      { toFun := fun g => Units.mk0 (D g i₀ i₀) (hDne g g.2 i₀) *
          (Units.mk0 (D g i₁ i₁) (hDne g g.2 i₁))⁻¹
        map_one' := by
          apply Units.ext
          have h1 : D ((1 : ↥P₁) : ↥P) = 1 := by
            simp only [hDdef, OneMemClass.coe_one, mul_one, inv_mul_cancel, Units.val_one]
          simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, h1,
            Matrix.one_apply_eq, inv_one, mul_one, Units.val_one]
        map_mul' := fun g g' => by
          apply Units.ext
          simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, Subgroup.coe_mul]
          rw [hDentry _ _ g.2 i₀, hDentry _ _ g.2 i₁, mul_inv]
          ring }
    have hχ3 : ∀ g : ↥P₁, χ g ^ 3 = 1 := by
      intro g
      rw [← map_pow]
      apply Units.ext
      have h1 : D (((g ^ 3 : ↥P₁) : ↥P)) = ((ψ (g : ↥P) : Kˣ) : K) • 1 := by
        have e1 : (((g ^ 3 : ↥P₁) : ↥P) : GL (Fin n) K) =
            GeneralLinearGroup.scalar (Fin n) (ψ (g : ↥P)) := by
          rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, hψ]
        simp only [hDdef]
        rw [e1, (commute_scalar (ψ (g : ↥P)) W⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one,
          GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, smul_one_eq_diagonal]
      change ((Units.mk0 (D _ i₀ i₀) _ * (Units.mk0 (D _ i₁ i₁) _)⁻¹ : Kˣ) : K) = 1
      simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, h1, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one]
      exact mul_inv_cancel₀ (ψ (g : ↥P)).ne_zero
    have hrange : χ.range ≤ rootsOfUnity 3 K := by
      rintro _ ⟨g, rfl⟩
      exact (mem_rootsOfUnity 3 _).2 (hχ3 g)
    have hkeridx : χ.ker.index ≤ 3 := by
      rw [Subgroup.index_ker]
      exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity K 3)
    set E : Subgroup (GL (Fin n) K) := (χ.ker.map P₁.subtype).map P.subtype with hE
    refine ⟨E, Subgroup.map_subtype_le _, ?_, t, htSU, ht2, htns, fun e he => ?_⟩
    · have hE1 : Nat.card E = Nat.card χ.ker := by
        rw [hE, Subgroup.card_map_of_injective P.subtype_injective,
          Subgroup.card_map_of_injective P₁.subtype_injective]
      have h1 := Subgroup.card_mul_index P₁
      have h2 := Subgroup.card_mul_index χ.ker
      rw [hE1]
      calc Nat.card P = Nat.card P₁ * P₁.index := h1.symm
        _ ≤ (Nat.card χ.ker * 3) * 3 := by
            rw [← h2]
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hkeridx) hP₁idx
        _ = 9 * Nat.card χ.ker := by ring
    · obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := he
      have hkd := hdiag (k : ↥P) k.2
      have hk1 : χ k = 1 := hk
      have heq : D (k : ↥P) i₀ i₀ = D (k : ↥P) i₁ i₁ := by
        have := congrArg (fun u : Kˣ => (u : K)) hk1
        simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val, Units.val_one] at this
        exact (mul_inv_eq_one₀ (hDne _ k.2 i₁)).1 this
      exact htc _ hkd heq

end Local

section InnerDiag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux
  CFSG.Open

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem scalar_mem_primeFormUnitary {z : Kˣ} (hz : h.norm (z : K) = 1) :
    GeneralLinearGroup.scalar (Fin n) z ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, hz,
    one_smul]

theorem exists_scalar_of_conjHom_eq_one (hn : 3 ≤ n)
    {A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hA : primeFormConjHom h _ A = 1) :
    ∃ z : Kˣ, (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) z := by
  have h1 : primeFormPsi h isPrimeFormGram_one ⟨A, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one]
    exact hA
  obtain ⟨-, z, -, hz⟩ := (primeFormPsi_eq_one_iff h isPrimeFormGram_one hn _).1 h1
  exact ⟨z, hz⟩

theorem starConcl_of_le_primeFormD [CharP K 2] (hq3 : 3 ∣ p ^ f + 1) (hn : 3 ≤ n)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian 3 D)
    (hDle : D ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    StarConcl D := by
  classical
  haveI : Finite K := h.finite
  haveI : Finite (GL (Fin n) K) := inferInstance
  set U := primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hUdef
  set c := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hcdef
  set PU : Subgroup ↥U := D.comap c with hPUdef
  set P : Subgroup (GL (Fin n) K) := PU.map U.subtype with hPdef
  have hPU : P ≤ U := Subgroup.map_subtype_le PU
  have hmemP : ∀ A : ↥U, (A : GL (Fin n) K) ∈ P ↔ c A ∈ D := fun A =>
    ⟨fun ⟨B, hB, hBA⟩ => by rw [← Subtype.ext hBA]; exact hB, fun hA => ⟨A, hA, rfl⟩⟩
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hZ : ∀ z : Kˣ, h.norm (z : K) = 1 → GeneralLinearGroup.scalar (Fin n) z ∈ P := by
    intro z hz
    have hzU := scalar_mem_primeFormUnitary h (n := n) hz
    refine (hmemP ⟨_, hzU⟩).2 ?_
    rw [hcdef, CFSG.RankThree.Classical.primeFormConjHom_scalar h n z hzU]
    exact one_mem D
  have hcube : ∀ g ∈ P, ∃ z : Kˣ, g ^ 3 = GeneralLinearGroup.scalar (Fin n) z := by
    rintro _ ⟨A, hA, rfl⟩
    have h1 : c (A ^ 3) = 1 := by rw [map_pow]; exact hD.2 _ hA
    obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn h1
    exact ⟨z, by rw [← hz]; rfl⟩
  have hcomm : ∀ g ∈ P, ∀ g' ∈ P, ∃ z : Kˣ,
      g * g' = GeneralLinearGroup.scalar (Fin n) z * (g' * g) := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    have h1 : c (A * B * A⁻¹ * B⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hDcomm _ hA _ hB]
      group
    obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn h1
    refine ⟨z, ?_⟩
    have hz' : (A : GL (Fin n) K) * B * (A : GL (Fin n) K)⁻¹ * (B : GL (Fin n) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) z := hz
    calc (A : GL (Fin n) K) * B = ((A : GL (Fin n) K) * B * (A : GL (Fin n) K)⁻¹ *
          (B : GL (Fin n) K)⁻¹) * (B * A) := by group
      _ = GeneralLinearGroup.scalar (Fin n) z * (B * A) := by rw [hz']
  obtain ⟨EG, hEGP, hcard, t, htSU, ht2, htns, htc⟩ :=
    exists_centralized_involution h hq3 (by omega) P hPU hZ hcube hcomm
  set EU : Subgroup ↥U := EG.comap U.subtype with hEUdef
  have hEUPU : EU ≤ PU := fun x hx => (hmemP x).1 (hEGP hx)
  set E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
    EU.map c with hEdef
  have hED : E ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hEUPU hx
  set tP : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ((⟨t, htSU⟩ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) with htPdef
  have htP2 : tP ^ 2 = 1 := by
    rw [htPdef, ← QuotientGroup.mk_pow]
    have : (⟨t, htSU⟩ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ht2)
    rw [this, QuotientGroup.mk_one]
  have htP1 : tP ≠ 1 := by
    intro h1
    rw [htPdef, QuotientGroup.eq_one_iff] at h1
    obtain ⟨z, -, -, hz⟩ := h1
    exact htns z hz
  have hEfix : ∀ φ ∈ E, φ tP = tP := by
    rintro _ ⟨x, hx, rfl⟩
    rw [htPdef, hcdef, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (x : GL (Fin n) K) * t * (x : GL (Fin n) K)⁻¹ = t
    rw [htc (x : GL (Fin n) K) hx, mul_inv_cancel_right]
  refine ⟨E, hED, ?_, Subgroup.zpowers tP, ?_, ?_, ?_⟩
  ·
    let fP : ↥PU →* ↥D := (c.comp PU.subtype).codRestrict D (fun x => x.2)
    have hfP : Function.Surjective fP := by
      rintro ⟨α, hα⟩
      obtain ⟨A, hA⟩ := hDle hα
      exact ⟨⟨A, show c A ∈ D by rw [hA]; exact hα⟩, Subtype.ext hA⟩
    have hmap : (EU.subgroupOf PU).map fP = E.subgroupOf D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.2 ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.1 hx
        exact ⟨⟨y, hEUPU hy⟩, Subgroup.mem_subgroupOf.2 hy, Subtype.ext hyx⟩
    have hcardPU : Nat.card PU = Nat.card P := by
      rw [hPdef, Subgroup.card_map_of_injective U.subtype_injective]
    have hEGU : EG ≤ U := hEGP.trans hPU
    have hmapEU : EU.map U.subtype = EG :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hEGU)
    have hcardEU : Nat.card (EU.subgroupOf PU) = Nat.card EG := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEUPU).toEquiv, ← hmapEU,
        Subgroup.card_map_of_injective U.subtype_injective]
    have hidxEU : (EU.subgroupOf PU).index ≤ 9 := by
      have h1 := Subgroup.card_mul_index (EU.subgroupOf PU)
      rw [hcardEU, hcardPU] at h1
      have hpos : 0 < Nat.card EG := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : 10 * Nat.card EG ≤ (EU.subgroupOf PU).index * Nat.card EG :=
        Nat.mul_le_mul_right _ hlt
      rw [mul_comm (EU.subgroupOf PU).index, h1] at this
      omega
    have hdvd := Subgroup.index_map_dvd (H := EU.subgroupOf PU) hfP
    rw [hmap] at hdvd
    have hne : (EU.subgroupOf PU).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hidxEU
  · intro hbot
    apply htP1
    have : tP ∈ Subgroup.zpowers tP := Subgroup.mem_zpowers tP
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · intro u
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 u.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, htP2, _root_.one_zpow, Subgroup.coe_one]
  · intro φ hφ u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, hEfix φ hφ]
    exact Subgroup.zpow_mem_zpowers tP k

end InnerDiag

section Restrict

theorem exists_restrict_hom {G H : Type*} [Group G] [Group H] (ι : H →* G)
    (hι : Function.Injective ι) (A : Subgroup (MulAut G))
    (hA : ∀ δ ∈ A, ∀ x : H, ∃ y : H, ι y = δ (ι x)) :
    ∃ ρ : ↥A →* MulAut H, ∀ (δ : ↥A) (x : H), ι (ρ δ x) = (δ : MulAut G) (ι x) := by
  classical
  let r : ↥A → H → H := fun δ x => (hA δ δ.2 x).choose
  have hr : ∀ δ x, ι (r δ x) = (δ : MulAut G) (ι x) := fun δ x => (hA δ δ.2 x).choose_spec
  have hrinv : ∀ δ x, r δ⁻¹ (r δ x) = x := fun δ x => hι (by
    rw [hr, hr, Subgroup.coe_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply])
  have hrinv' : ∀ δ x, r δ (r δ⁻¹ x) = x := fun δ x => hι (by
    rw [hr, hr, Subgroup.coe_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply])
  let ρ₀ : ↥A → MulAut H := fun δ =>
    { toFun := r δ
      invFun := r δ⁻¹
      left_inv := hrinv δ
      right_inv := hrinv' δ
      map_mul' := fun x y => hι (by rw [hr, map_mul, map_mul, map_mul, hr, hr]) }
  refine ⟨{ toFun := ρ₀, map_one' := ?_, map_mul' := ?_ }, fun δ x => hr δ x⟩
  · ext x
    apply hι
    change ι (r 1 x) = ι x
    rw [hr]
    rfl
  · intro δ δ'
    ext x
    apply hι
    change ι (r (δ * δ') x) = ι (r δ (r δ' x))
    rw [hr, hr, hr]
    rfl

end Restrict

section TwoEight

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux
  CFSG.Open CFSG.LieType.Chevalley

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem starConcl_two (h : UnitaryFieldData p f K) (hp : p = 2) (hf : f = 1) (hn : 4 ≤ n)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian 3 D) : StarConcl D := by
  subst hp hf
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  refine starConcl_of_le_primeFormD h (by norm_num) hn3 D hD ?_
  intro β hβ
  rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hq, MonoidHom.mem_ker]
  set θ := primeFormFieldFactor h isPrimeFormGram_one hn3 hq β
  have hcard : Nat.card (RingAut K) = 2 :=
    (card_ringAut_and_isCyclic Nat.prime_two K (h.card.trans (by norm_num))).1
  haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h2 : θ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := RingAut K) (x := θ)
    rwa [hcard] at this
  have h3 : θ ^ 3 = 1 := by rw [← map_pow, hD.2 β hβ, map_one]
  calc θ = θ ^ 3 * (θ ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, one_mul, inv_one]

theorem mulAut_congr_eq {G : Type*} [Group G] (φ α : MulAut G) :
    MulAut.congr φ α = φ * α * φ⁻¹ := by
  ext x
  simp [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem starConcl_eight (h : UnitaryFieldData p f K) (hp : p = 2) (hf : f = 3) (hn : 4 ≤ n)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian 3 D) : StarConcl D := by
  subst hp hf
  classical
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 3 = 2) := by omega
  haveI : Finite (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
    MulEquiv.finite_left
  set Θ := primeFormFieldFactor h isPrimeFormGram_one hn3 hq with hΘ
  have hkerΘ := ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hq
  by_cases hDle : D ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  · exact starConcl_of_le_primeFormD h (by norm_num) hn3 D hD hDle
  obtain ⟨b, hbD, hbout⟩ := Set.not_subset.1 hDle
  have hb3 : b ^ 3 = 1 := hD.2 b hbD
  set σ := Θ b with hσdef
  have hσ1 : σ ≠ 1 := fun h1 => hbout (by rw [← hkerΘ]; exact h1)
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hb3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hb1 : b ≠ 1 := fun h1 => hσ1 (by rw [hσdef, h1, map_one])
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hq Nat.prime_three
      (by norm_num) (by norm_num) b hbord σ rfl hσord
  set cM := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hcM
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  refine starConcl_of_congr cM⁻¹ D ?_
  set D' := D.map (MulAut.congr cM⁻¹).toMonoidHom with hD'
  have hD'el : IsElemAbelian 3 D' := hD.map _
  have hfσD' : fσ ∈ D' := ⟨b, hbD, by
    simp only [MulEquiv.coe_toMonoidHom]
    rw [mulAut_congr_eq, inv_inv, hM]⟩
  have hΘfσ : Θ fσ = σ := by
    have := primeFormFieldFactor_apply h isPrimeFormGram_one hn3 hq 1 σ
    rwa [map_one, one_mul] at this
  have hfσout : fσ ∉ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← hkerΘ, MonoidHom.mem_ker, hΘfσ]
    exact hσ1
  set D'₀ := D' ⊓ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD'₀
  have hcard3 : Nat.card D' ≤ 3 * Nat.card D'₀ := by
    have hRcard : Nat.card (RingAut K) = 6 :=
      (card_ringAut_and_isCyclic Nat.prime_two K (h.card.trans (by norm_num))).1
    haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hRcard]; norm_num)
    let fD : ↥D' →* RingAut K := Θ.comp D'.subtype
    have hker : Nat.card fD.ker ≤ Nat.card D'₀ := by
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥D') : MulAut _), ?_⟩) ?_
      · refine Subgroup.mem_inf.2 ⟨(x : ↥D').2, ?_⟩
        rw [← hkerΘ, MonoidHom.mem_ker]
        exact x.2
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        simp only at h1
        exact Subtype.ext (Subtype.ext h1)
    have hr3 : Nat.card fD.range ≤ 3 := by
      have hpg : IsPGroup 3 fD.range := by
        rintro ⟨_, ⟨x, rfl⟩⟩
        refine ⟨1, Subtype.ext ?_⟩
        simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
        rw [← map_pow]
        have : x ^ 3 = 1 := Subtype.ext (by simpa using hD'el.2 x x.2)
        rw [this, map_one]
      obtain ⟨m, hm⟩ := hpg.exists_card_eq
      have hdvd : Nat.card fD.range ∣ 6 := hRcard ▸ Subgroup.card_subgroup_dvd_card _
      rw [hm] at hdvd ⊢
      have hm1 : m ≤ 1 := by
        by_contra hm2
        push Not at hm2
        have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 hm2).trans hdvd
        norm_num at this
      interval_cases m <;> norm_num
    have h1 := Subgroup.card_mul_index fD.ker
    rw [Subgroup.index_ker] at h1
    calc Nat.card D' = Nat.card fD.ker * Nat.card fD.range := h1.symm
      _ ≤ Nat.card D'₀ * 3 := Nat.mul_le_mul hker hr3
      _ = 3 * Nat.card D'₀ := mul_comm _ _
  have h₀ : UnitaryFieldData 2 (3 / 3) ↥(fixSubfield σ) :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσord
  have hbar : ∀ c : ↥(fixSubfield σ), (h₀.bar c : K) = h.bar c :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσord
  set ι := CFSG.RankThree.Classical.subfieldPSU h h₀ hbar n with hιdef
  have hιinj : Function.Injective ι :=
    CFSG.RankThree.Classical.subfieldPSU_injective h h₀ hbar n hn1
  have hfσY : ∀ y, fσ (ι y) = ι y := fun y =>
    CFSG.RankThree.Classical.range_subfieldPSU_le h n h₀ hbar ⟨y, rfl⟩
  have hpres : ∀ δ ∈ D'₀, ∀ x, ∃ y, ι y = δ (ι x) := by
    rintro δ ⟨hδD', B, rfl⟩ x
    have hcomm : primeFormConjHom h _ B * fσ = fσ * primeFormConjHom h _ B :=
      congrArg Subtype.val (hD'el.1.is_comm.comm ⟨_, hδD'⟩ ⟨fσ, hfσD'⟩)
    have hσB : primeFormConjHom h _ (primeFormFieldU h isPrimeFormGram_one σ B) =
        primeFormConjHom h _ B := by
      rw [← primeFormField_conj_eq, ← hcomm, mul_inv_cancel_right]
    obtain ⟨l, hl⟩ := exists_scalar_of_conjHom_eq_one h hn3
      (A := primeFormFieldU h isPrimeFormGram_one σ B * B⁻¹) (by
        rw [map_mul, map_inv, hσB, mul_inv_cancel])
    have hσB' : glAut σ (B : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) l * B := by
      have e1 : glAut σ (B : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ =
          GeneralLinearGroup.scalar (Fin n) l := by
        rw [← hl, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU]
      rw [← e1, inv_mul_cancel_right]
    induction x using QuotientGroup.induction_on with
    | H g₀ =>
      set M : GL (Fin n) K := (B : GL (Fin n) K) *
        CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n (g₀ : GL (Fin n) ↥(fixSubfield σ)) *
          (B : GL (Fin n) K)⁻¹ with hMdef
      have hfix0 : glAut σ (CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n
          (g₀ : GL (Fin n) ↥(fixSubfield σ))) =
          CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n
            (g₀ : GL (Fin n) ↥(fixSubfield σ)) := by
        apply Units.ext
        rw [coe_glAut, CFSG.RankThree.Classical.coe_subfieldGL]
        ext i j
        simp only [Matrix.map_apply]
        exact (mem_fixSubfield σ).1
          (((g₀ : GL (Fin n) ↥(fixSubfield σ)) : Matrix (Fin n) (Fin n) ↥(fixSubfield σ)) i j).2
      have hMfix : glAut σ M = M := by
        rw [hMdef, map_mul, map_mul, map_inv, hσB', hfix0, _root_.mul_inv_rev]
        set G₀ := CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n
          (g₀ : GL (Fin n) ↥(fixSubfield σ))
        have hc : ∀ g : GL (Fin n) K, GeneralLinearGroup.scalar (Fin n) l * g =
            g * GeneralLinearGroup.scalar (Fin n) l := fun g => ((commute_scalar l g).eq).symm
        calc GeneralLinearGroup.scalar (Fin n) l * (B : GL (Fin n) K) * G₀ *
              ((B : GL (Fin n) K)⁻¹ * (GeneralLinearGroup.scalar (Fin n) l)⁻¹) =
            GeneralLinearGroup.scalar (Fin n) l * ((B : GL (Fin n) K) * G₀ * (B : GL (Fin n) K)⁻¹) *
              (GeneralLinearGroup.scalar (Fin n) l)⁻¹ := by group
          _ = (B : GL (Fin n) K) * G₀ * (B : GL (Fin n) K)⁻¹ := by
              rw [hc, mul_inv_cancel_right]
      obtain ⟨g₀', hg₀'⟩ := CFSG.RankThree.Classical.exists_subfieldGL_eq_of_fixed n hMfix
      have hMSU : M ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        conj_mem_gramSU h _ B.2
          (CFSG.RankThree.Classical.subfieldGL_mem_gramSU h h₀ hbar n g₀.2)
      have hg₀'SU : g₀' ∈ gramSU h₀ ((1 : GL (Fin n) ↥(fixSubfield σ)) :
          Matrix (Fin n) (Fin n) ↥(fixSubfield σ)) :=
        CFSG.RankThree.Classical.mem_gramSU_of_subfieldGL h n h₀ hbar (by rw [hg₀']; exact hMSU)
      refine ⟨((⟨g₀', hg₀'SU⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
      rw [hιdef, CFSG.RankThree.Classical.subfieldPSU_mk, CFSG.RankThree.Classical.subfieldPSU_mk,
        primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      rw [CFSG.RankThree.Classical.coe_subfieldSU]
      change CFSG.RankThree.Classical.subfieldGL (fixSubfield σ) n g₀' = M
      exact hg₀'
  obtain ⟨ρ, hρ⟩ := exists_restrict_hom ι hιinj D'₀ hpres
  have hρel : IsElemAbelian 3 ρ.range := by
    have h1 := (hD'el.mono (inf_le_left : D'₀ ≤ D')).subgroupOf D'₀
    rw [Subgroup.subgroupOf_self] at h1
    rw [MonoidHom.range_eq_map]
    exact h1.map ρ
  obtain ⟨E'', hE''le, hE''idx, U'', hU''ne, hU''2, hU''inv⟩ :=
    starConcl_two h₀ rfl (by norm_num) hn ρ.range hρel
  set E₀' : Subgroup ↥D'₀ := E''.comap ρ with hE₀'
  have hE₀'idx : E₀'.index ≤ 9 := by
    rw [hE₀', Subgroup.index_comap]
    exact hE''idx
  set E₀ := E₀'.map D'₀.subtype with hE₀
  have hE₀D'₀ : E₀ ≤ D'₀ := Subgroup.map_subtype_le _
  have hcardE₀ : Nat.card E₀ = Nat.card E₀' :=
    Subgroup.card_map_of_injective D'₀.subtype_injective
  have hcardD'₀ : Nat.card D'₀ ≤ 9 * Nat.card E₀ := by
    have := Subgroup.card_mul_index E₀'
    rw [hcardE₀, ← this, mul_comm]
    exact Nat.mul_le_mul_right _ hE₀'idx
  set U := U''.map ι with hUdef
  set E := Subgroup.zpowers fσ ⊔ E₀ with hEdef
  have hED' : E ≤ D' := sup_le (Subgroup.zpowers_le.2 hfσD') (hE₀D'₀.trans inf_le_left)
  let Nstab : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
    { carrier := {φ | ∀ u, u ∈ U ↔ φ u ∈ U}
      mul_mem' := fun {φ ψ} hφ hψ u => (hψ u).trans (hφ (ψ u))
      one_mem' := fun u => Iff.rfl
      inv_mem' := fun {φ} hφ u => by
        have := hφ (φ⁻¹ u)
        rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
        rw [MulAut.inv_apply]
        exact this.symm }
  have hfσN : fσ ∈ Nstab := by
    intro u
    constructor
    · rintro ⟨u'', hu'', rfl⟩
      rw [hfσY]
      exact ⟨u'', hu'', rfl⟩
    · rintro ⟨u'', hu'', hu⟩
      have : u = ι u'' := fσ.injective (by rw [hfσY]; exact hu.symm)
      rw [this]
      exact ⟨u'', hu'', rfl⟩
  have hE₀N : E₀ ≤ Nstab := by
    have hfwd : ∀ k ∈ E₀', ∀ u ∈ U, (k : MulAut _) u ∈ U := by
      rintro k hk _ ⟨u'', hu'', rfl⟩
      rw [← hρ]
      exact ⟨_, hU''inv _ hk u'' hu'', rfl⟩
    rintro _ ⟨k, hk, rfl⟩ u
    have hk' : (D'₀.subtype k : MulAut _) = (k : MulAut _) := rfl
    rw [hk']
    constructor
    · exact hfwd k hk u
    · intro hu
      have := hfwd k⁻¹ (inv_mem hk) _ hu
      rwa [Subgroup.coe_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply] at this
  have hEN : E ≤ Nstab := sup_le (Subgroup.zpowers_le.2 hfσN) hE₀N
  refine ⟨E, hED', ?_, U, ?_, hU''2.map ι, fun φ hφ u hu => (hEN hφ u).1 hu⟩
  · refine relIndex_le_of_card_le hED' (n := 9) ?_
    have hE₀E : E₀ ≤ E := le_sup_right
    have hidx3 : 3 ≤ E₀.relIndex E := by
      have hdvd : E₀.relIndex E ∣ Nat.card E := Subgroup.relIndex_dvd_card _ _
      have hEp : IsPGroup 3 E := (hD'el.mono hED').isPGroup
      obtain ⟨m, hm⟩ := hEp.exists_card_eq
      rw [hm] at hdvd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      have hne : E₀.relIndex E ≠ 1 := by
        intro h1
        have hle := (Subgroup.relIndex_eq_one).1 h1
        exact hfσout (hE₀D'₀ (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers fσ)))).2
      rw [hj] at hne ⊢
      have : j ≠ 0 := by
        rintro rfl
        exact hne (pow_zero 3)
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 this)
    have hcardE : 3 * Nat.card E₀ ≤ Nat.card E := by
      have h := Subgroup.relIndex_mul_card E₀ E
      rw [inf_of_le_left hE₀E] at h
      rw [← h]
      exact Nat.mul_le_mul_right _ hidx3
    omega
  · intro hbot
    exact hU''ne ((Subgroup.map_eq_bot_iff_of_injective U'' hιinj).1 hbot)

end TwoEight

section Main

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux
  CFSG.Open

theorem star2313UnitaryInput_holds : Star2313UnitaryInput := by
  intro S _ _ r q hv hd hS D hD
  obtain ⟨eS⟩ := hS
  obtain ⟨hq13, m, hm3, hrm⟩ := hd
  obtain ⟨⟨hℓ, hf, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eS
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hn : 4 ≤ r + 1 := by omega
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := K))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  refine starConcl_of_congr e D ?_
  rcases hq13 with ⟨hp, he⟩ | ⟨hp, he⟩
  · exact starConcl_two h hp he hn _ (hD.map _)
  · exact starConcl_eight h hp he hn _ (hD.map _)

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof
