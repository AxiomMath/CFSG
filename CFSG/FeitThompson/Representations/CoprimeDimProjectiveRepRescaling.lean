module

public import CFSG.FeitThompson.Representations.CocyclePowerCoboundary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix

section GeneralLinear

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

theorem scalar_mem_center_gl (u : Kˣ) :
    GeneralLinearGroup.scalar ι u ∈ Subgroup.center (GL ι K) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩

theorem commute_scalar_gl (u : Kˣ) (A : GL ι K) : Commute (GeneralLinearGroup.scalar ι u) A :=
  (Subgroup.mem_center_iff.mp (scalar_mem_center_gl u) A).symm

theorem units_smul_gl_eq_scalar_mul (u : Kˣ) (A : GL ι K) :
    u • A = GeneralLinearGroup.scalar ι u * A := by
  ext i j
  simp [Units.smul_def, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem units_smul_gl_mul_units_smul_gl (u v : Kˣ) (A C : GL ι K) :
    (u • A) * (v • C) = (u * v) • (A * C) := by
  simp only [units_smul_gl_eq_scalar_mul, map_mul]
  rw [mul_assoc, mul_assoc, ← mul_assoc A, (commute_scalar_gl v A).symm.eq, mul_assoc]

theorem units_smul_gl_mul (u : Kˣ) (A C : GL ι K) : (u • A) * C = u • (A * C) := by
  simpa using units_smul_gl_mul_units_smul_gl u 1 A C

theorem gl_mul_units_smul_gl (u : Kˣ) (A C : GL ι K) : A * (u • C) = u • (A * C) := by
  simpa using units_smul_gl_mul_units_smul_gl 1 u A C

theorem det_units_smul_gl (u : Kˣ) (A : GL ι K) :
    GeneralLinearGroup.det (u • A) = u ^ Fintype.card ι * GeneralLinearGroup.det A := by
  rw [units_smul_gl_eq_scalar_mul, map_mul, GeneralLinearGroup.det_scalar]

theorem units_smul_gl_left_cancel [Nonempty ι] {u v : Kˣ} {A : GL ι K} (h : u • A = v • A) :
    u = v := by
  rw [units_smul_gl_eq_scalar_mul, units_smul_gl_eq_scalar_mul] at h
  have h' : Matrix.scalar ι (u : K) = Matrix.scalar ι (v : K) := by
    simpa [GeneralLinearGroup.coe_scalar] using
      congrArg (fun M : GL ι K => (M : Matrix ι ι K)) (mul_right_cancel h)
  exact Units.ext (Matrix.scalar_inj.mp h')

end GeneralLinear

theorem mul_eq_of_pow_mul_eq {N : Type*} [CommGroup N] {u a₁ a₂ a₃ b₁ b₂ b₃ : N} {d m : ℕ}
    {r s : ℤ} (hrs : (d : ℤ) * r + (m : ℤ) * s = 1)
    (ha : u ^ d * a₃ = a₁ * a₂) (hb : u ^ m * b₃ = b₁ * b₂) :
    u * (a₃ ^ r * b₃ ^ s) = (a₁ ^ r * b₁ ^ s) * (a₂ ^ r * b₂ ^ s) := by
  have hu : u = (u ^ (d : ℤ)) ^ r * (u ^ (m : ℤ)) ^ s := by
    rw [← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add, hrs, zpow_one]
  calc u * (a₃ ^ r * b₃ ^ s)
      = ((u ^ (d : ℤ)) ^ r * (u ^ (m : ℤ)) ^ s) * (a₃ ^ r * b₃ ^ s) := by rw [← hu]
    _ = (u ^ (d : ℤ) * a₃) ^ r * (u ^ (m : ℤ) * b₃) ^ s := by
        rw [mul_zpow, mul_zpow]; exact mul_mul_mul_comm _ _ _ _
    _ = (a₁ * a₂) ^ r * (b₁ * b₂) ^ s := by rw [zpow_natCast, zpow_natCast, ha, hb]
    _ = (a₁ ^ r * b₁ ^ s) * (a₂ ^ r * b₂ ^ s) := by
        rw [mul_zpow, mul_zpow]; exact mul_mul_mul_comm _ _ _ _

section Projective

variable {Q ι K : Type*} [Group Q] [Fintype ι] [DecidableEq ι] [CommRing K]
  {B : Q → GL ι K} {α : Q → Q → Kˣ}

theorem factorSet_one_left [Nonempty ι] (hB1 : B 1 = 1)
    (hB : ∀ x y, B x * B y = α x y • B (x * y)) (z : Q) : α 1 z = 1 := by
  refine units_smul_gl_left_cancel (A := B z) ?_
  have h := hB 1 z
  rw [hB1, one_mul, one_mul] at h
  simpa using h.symm

theorem factorSet_one_right [Nonempty ι] (hB1 : B 1 = 1)
    (hB : ∀ x y, B x * B y = α x y • B (x * y)) (x : Q) : α x 1 = 1 := by
  refine units_smul_gl_left_cancel (A := B x) ?_
  have h := hB x 1
  rw [hB1, mul_one, mul_one] at h
  simpa using h.symm

theorem factorSet_cocycle [Nonempty ι] (hB : ∀ x y, B x * B y = α x y • B (x * y)) (x y z : Q) :
    α x y * α (x * y) z = α x (y * z) * α y z := by
  refine units_smul_gl_left_cancel (A := B (x * y * z)) ?_
  calc (α x y * α (x * y) z) • B (x * y * z)
      = (B x * B y) * B z := by rw [← smul_smul, ← hB, ← units_smul_gl_mul, ← hB]
    _ = B x * (B y * B z) := mul_assoc _ _ _
    _ = (α x (y * z) * α y z) • B (x * y * z) := by
        rw [hB y z, gl_mul_units_smul_gl, hB x (y * z), smul_smul, mul_comm (α y z), mul_assoc]

theorem pow_card_mul_det (hB : ∀ x y, B x * B y = α x y • B (x * y)) (x y : Q) :
    α x y ^ Fintype.card ι * GeneralLinearGroup.det (B (x * y)) =
      GeneralLinearGroup.det (B x) * GeneralLinearGroup.det (B y) := by
  rw [← det_units_smul_gl, ← hB, map_mul]

def projLinearization (B : Q → GL ι K) (c : Q → Kˣ) (x : Q) : GL ι K := (c x)⁻¹ • B x

omit [Group Q] in
theorem projLinearization_apply (B : Q → GL ι K) (c : Q → Kˣ) (x : Q) :
    projLinearization B c x = (c x)⁻¹ • B x := (rfl)

theorem projLinearization_one (hB1 : B 1 = 1) {c : Q → Kˣ} (hc1 : c 1 = 1) :
    projLinearization B c 1 = 1 := by
  rw [projLinearization_apply, hB1, hc1, inv_one, one_smul]

theorem projLinearization_mul (hB : ∀ x y, B x * B y = α x y • B (x * y)) {c : Q → Kˣ}
    (hc : ∀ x y, α x y * c (x * y) = c x * c y) (x y : Q) :
    projLinearization B c x * projLinearization B c y = projLinearization B c (x * y) := by
  rw [projLinearization_apply, projLinearization_apply, projLinearization_apply,
    units_smul_gl_mul_units_smul_gl, hB, smul_smul]
  congr 1
  rw [eq_inv_iff_mul_eq_one, mul_assoc, hc, mul_comm ((c x)⁻¹), ← mul_inv, mul_comm (c y),
    inv_mul_cancel]

def projLinearizationHom (B : Q → GL ι K) {α : Q → Q → Kˣ} {c : Q → Kˣ} (hB1 : B 1 = 1)
    (hB : ∀ x y, B x * B y = α x y • B (x * y)) (hc1 : c 1 = 1)
    (hc : ∀ x y, α x y * c (x * y) = c x * c y) : Q →* GL ι K where
  toFun := projLinearization B c
  map_one' := projLinearization_one hB1 hc1
  map_mul' x y := (projLinearization_mul hB hc x y).symm

theorem projLinearizationHom_apply (B : Q → GL ι K) {α : Q → Q → Kˣ} {c : Q → Kˣ}
    (hB1 : B 1 = 1) (hB : ∀ x y, B x * B y = α x y • B (x * y)) (hc1 : c 1 = 1)
    (hc : ∀ x y, α x y * c (x * y) = c x * c y) (x : Q) :
    projLinearizationHom B hB1 hB hc1 hc x = (c x)⁻¹ • B x := (rfl)

section Explicit

variable [Fintype Q]

def projRescale (B : Q → GL ι K) (α : Q → Q → Kˣ) (r s : ℤ) (x : Q) : Kˣ :=
  GeneralLinearGroup.det (B x) ^ r * cocycleProd α x ^ s

omit [Group Q] in
theorem projRescale_apply (B : Q → GL ι K) (α : Q → Q → Kˣ) (r s : ℤ) (x : Q) :
    projRescale B α r s x = GeneralLinearGroup.det (B x) ^ r * cocycleProd α x ^ s := (rfl)

theorem projRescale_one [Nonempty ι] (hB1 : B 1 = 1)
    (hB : ∀ x y, B x * B y = α x y • B (x * y)) (r s : ℤ) : projRescale B α r s 1 = 1 := by
  rw [projRescale_apply, hB1, cocycleProd_one (factorSet_one_left hB1 hB)]
  simp

theorem factorSet_mul_projRescale [Nonempty ι]
    (hB : ∀ x y, B x * B y = α x y • B (x * y)) {r s : ℤ}
    (hrs : (Fintype.card ι : ℤ) * r + (Nat.card Q : ℤ) * s = 1) (x y : Q) :
    α x y * projRescale B α r s (x * y) = projRescale B α r s x * projRescale B α r s y :=
  mul_eq_of_pow_mul_eq hrs (pow_card_mul_det hB x y)
    (pow_natCard_mul_cocycleProd (factorSet_cocycle hB) x y)

end Explicit

theorem exists_projLinearization [Finite Q] [Nonempty ι]
    (hcop : (Fintype.card ι).Coprime (Nat.card Q)) (hB1 : B 1 = 1)
    (hB : ∀ x y, B x * B y = α x y • B (x * y)) :
    ∃ (c : Q → Kˣ) (T : Q →* GL ι K), c 1 = 1 ∧ ∀ x, T x = (c x)⁻¹ • B x := by
  cases nonempty_fintype Q
  set d := Fintype.card ι
  set m := Nat.card Q
  have hrs : (d : ℤ) * Nat.gcdA d m + (m : ℤ) * Nat.gcdB d m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop]; norm_num
  exact ⟨projRescale B α (Nat.gcdA d m) (Nat.gcdB d m),
    projLinearizationHom B hB1 hB (projRescale_one hB1 hB _ _)
      (factorSet_mul_projRescale hB hrs), projRescale_one hB1 hB _ _, fun _ => (rfl)⟩

end Projective

section Matrices

variable {Q ι K : Type*} [Group Q] [Fintype ι] [DecidableEq ι] [Nonempty ι] [Field K]
  {B : Q → Matrix ι ι K} {α : Q → Q → K}

theorem exists_matrix_projLinearization [Finite Q]
    (hcop : (Fintype.card ι).Coprime (Nat.card Q))
    (hBu : ∀ x, IsUnit (B x).det) (hB1 : B 1 = 1) (hα : ∀ x y, α x y ≠ 0)
    (hB : ∀ x y, B x * B y = α x y • B (x * y)) :
    ∃ c : Q → K, c 1 = 1 ∧ (∀ x, c x ≠ 0) ∧
      (∀ x y, ((c x)⁻¹ • B x) * ((c y)⁻¹ • B y) = (c (x * y))⁻¹ • B (x * y)) := by
  set Bg : Q → GL ι K := fun x => GeneralLinearGroup.mk'' (B x) (hBu x) with hBg
  set αu : Q → Q → Kˣ := fun x y => Units.mk0 (α x y) (hα x y) with hαu
  have hBg1 : Bg 1 = 1 := by ext i j; simp [hBg, GeneralLinearGroup.val_mk'', hB1]
  have hBgm : ∀ x y, Bg x * Bg y = αu x y • Bg (x * y) := by
    intro x y
    ext i j
    simp [hBg, hαu, GeneralLinearGroup.val_mk'', Units.smul_def, hB x y]
  obtain ⟨c, T, hc1, hT⟩ := exists_projLinearization hcop hBg1 hBgm
  refine ⟨fun x => (c x : K), by simpa using congrArg (Units.val (α := K)) hc1,
    fun x => (c x).ne_zero, fun x y => ?_⟩
  have key : T x * T y = T (x * y) := (T.map_mul x y).symm
  rw [hT, hT, hT] at key
  have h2 := congrArg (fun M : GL ι K => (M : Matrix ι ι K)) key
  simpa [hBg, GeneralLinearGroup.val_mk'', Units.smul_def, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul] using h2

end Matrices

end CFSG.FeitThompson
