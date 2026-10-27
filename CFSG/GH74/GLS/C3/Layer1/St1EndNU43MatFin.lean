module

public import CFSG.LieType.Multipliers.U43Field
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat

open CFSG.LieType.Multipliers.U43 (F9)
open Matrix

abbrev f9 (a b : ZMod 3) : F9 := ⟨a, b⟩

@[expose] def barF (x : F9) : F9 := ⟨x.re, -x.im⟩

structure V4 where
  x0 : F9
  x1 : F9
  x2 : F9
  x3 : F9
  deriving DecidableEq

structure M4 where
  a00 : F9
  a01 : F9
  a02 : F9
  a03 : F9
  a10 : F9
  a11 : F9
  a12 : F9
  a13 : F9
  a20 : F9
  a21 : F9
  a22 : F9
  a23 : F9
  a30 : F9
  a31 : F9
  a32 : F9
  a33 : F9
  deriving DecidableEq

@[expose] def M4.toMat : M4 → Matrix (Fin 4) (Fin 4) F9
  | ⟨a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩ =>
    !![a00, a01, a02, a03;
      a10, a11, a12, a13;
      a20, a21, a22, a23;
      a30, a31, a32, a33]

@[expose] def V4.toVec : V4 → (Fin 4 → F9)
  | ⟨a, b, c, d⟩ => ![a, b, c, d]

@[expose] def V4.ofVec (u : Fin 4 → F9) : V4 :=
  ⟨u 0, u 1, u 2, u 3⟩

@[expose] def M4.mul : M4 → M4 → M4
  | ⟨a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩,
    ⟨b00, b01, b02, b03, b10, b11, b12, b13, b20, b21, b22, b23, b30, b31, b32, b33⟩ =>
    ⟨a00 * b00 + a01 * b10 + a02 * b20 + a03 * b30,
      a00 * b01 + a01 * b11 + a02 * b21 + a03 * b31,
      a00 * b02 + a01 * b12 + a02 * b22 + a03 * b32,
      a00 * b03 + a01 * b13 + a02 * b23 + a03 * b33,
      a10 * b00 + a11 * b10 + a12 * b20 + a13 * b30,
      a10 * b01 + a11 * b11 + a12 * b21 + a13 * b31,
      a10 * b02 + a11 * b12 + a12 * b22 + a13 * b32,
      a10 * b03 + a11 * b13 + a12 * b23 + a13 * b33,
      a20 * b00 + a21 * b10 + a22 * b20 + a23 * b30,
      a20 * b01 + a21 * b11 + a22 * b21 + a23 * b31,
      a20 * b02 + a21 * b12 + a22 * b22 + a23 * b32,
      a20 * b03 + a21 * b13 + a22 * b23 + a23 * b33,
      a30 * b00 + a31 * b10 + a32 * b20 + a33 * b30,
      a30 * b01 + a31 * b11 + a32 * b21 + a33 * b31,
      a30 * b02 + a31 * b12 + a32 * b22 + a33 * b32,
      a30 * b03 + a31 * b13 + a32 * b23 + a33 * b33⟩

@[expose] def M4.mulV : M4 → V4 → V4
  | ⟨a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩,
    ⟨v0, v1, v2, v3⟩ =>
    ⟨a00 * v0 + a01 * v1 + a02 * v2 + a03 * v3,
      a10 * v0 + a11 * v1 + a12 * v2 + a13 * v3,
      a20 * v0 + a21 * v1 + a22 * v2 + a23 * v3,
      a30 * v0 + a31 * v1 + a32 * v2 + a33 * v3⟩

@[expose] def M4.smul (c : F9) : M4 → M4
  | ⟨a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩ =>
    ⟨c * a00, c * a01, c * a02, c * a03, c * a10, c * a11, c * a12, c * a13,
      c * a20, c * a21, c * a22, c * a23, c * a30, c * a31, c * a32, c * a33⟩

@[expose] def M4.map (ψ : F9 → F9) : M4 → M4
  | ⟨a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩ =>
    ⟨ψ a00, ψ a01, ψ a02, ψ a03, ψ a10, ψ a11, ψ a12, ψ a13,
      ψ a20, ψ a21, ψ a22, ψ a23, ψ a30, ψ a31, ψ a32, ψ a33⟩

@[expose] def V4.map (ψ : F9 → F9) : V4 → V4
  | ⟨a, b, c, d⟩ => ⟨ψ a, ψ b, ψ c, ψ d⟩

@[expose] def zM4 : M4 :=
  ⟨f9 0 0, f9 2 2, f9 0 0, f9 1 1,
    f9 0 0, f9 1 2, f9 0 0, f9 1 2,
    f9 2 2, f9 0 0, f9 1 1, f9 0 0,
    f9 2 1, f9 0 0, f9 2 1, f9 0 0⟩

@[expose] def kInvId4 : M4 :=
  ⟨f9 1 0, f9 1 0, f9 2 2, f9 2 1,
    f9 0 0, f9 0 1, f9 2 0, f9 1 2,
    f9 0 0, f9 2 1, f9 1 0, f9 0 2,
    f9 0 0, f9 0 2, f9 0 1, f9 1 0⟩

@[expose] def kInvBar4 : M4 :=
  ⟨f9 1 0, f9 1 0, f9 2 1, f9 2 2,
    f9 0 0, f9 0 2, f9 2 0, f9 1 1,
    f9 0 0, f9 2 2, f9 1 0, f9 0 1,
    f9 0 0, f9 0 1, f9 0 2, f9 1 0⟩

@[expose] def gA4 : M4 :=
  ⟨f9 0 0, f9 2 2, f9 1 2, f9 0 0,
    f9 1 2, f9 0 0, f9 0 0, f9 2 1,
    f9 2 2, f9 0 0, f9 0 0, f9 2 2,
    f9 0 0, f9 1 1, f9 1 2, f9 0 0⟩

@[expose] def gB4 : M4 :=
  ⟨f9 0 1, f9 1 2, f9 0 1, f9 0 0,
    f9 2 2, f9 0 0, f9 1 1, f9 0 0,
    f9 0 1, f9 2 1, f9 0 1, f9 0 0,
    f9 0 0, f9 0 0, f9 0 0, f9 0 1⟩

@[expose] def gC4 : M4 :=
  ⟨f9 0 1, f9 0 0, f9 0 0, f9 0 0,
    f9 0 0, f9 0 0, f9 1 2, f9 2 2,
    f9 0 0, f9 2 2, f9 0 1, f9 2 0,
    f9 0 0, f9 1 2, f9 1 0, f9 0 1⟩

@[expose] def zM : Matrix (Fin 4) (Fin 4) F9 := zM4.toMat

@[expose] def gA : Matrix (Fin 4) (Fin 4) F9 := gA4.toMat

@[expose] def gB : Matrix (Fin 4) (Fin 4) F9 := gB4.toMat

@[expose] def gC : Matrix (Fin 4) (Fin 4) F9 := gC4.toMat

@[expose] def mu4 : List F9 := [1, -1, f9 0 1, f9 0 2]

@[expose] def qOf (g : Matrix (Fin 4) (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9 :=
  zM * g * zM * (g.map barF)ᵀ

theorem zM_pow_five : zM ^ 5 = 1 := by decide

theorem zM_unitary : (zM.map barF)ᵀ * zM = 1 := by decide

theorem zM_det : zM.det = 1 := by decide

theorem zM_not_scalar : ∀ c : F9, zM ≠ c • 1 := by decide

theorem mu4_pow_four : ∀ lam ∈ mu4, lam ^ 4 = 1 := by decide

theorem gA_unitary : (gA.map barF)ᵀ * gA = 1 := by decide

theorem gB_unitary : (gB.map barF)ᵀ * gB = 1 := by decide

theorem gC_unitary : (gC.map barF)ᵀ * gC = 1 := by decide

theorem gA_det : gA.det = 1 := by decide

theorem gB_det : gB.det = 1 := by decide

theorem gC_det : gC.det = 1 := by decide

theorem qA_sq : qOf gA * qOf gA = (-1 : F9) • 1 := by decide

theorem qB_sq : qOf gB * qOf gB = (1 : F9) • 1 := by decide

theorem qC_sq : qOf gC * qOf gC = (1 : F9) • 1 := by decide

theorem qA_ne : ∀ c : F9, qOf gA ≠ c • 1 := by decide

theorem qB_ne : ∀ c : F9, qOf gB ≠ c • 1 := by decide

theorem qC_ne : ∀ c : F9, qOf gC ≠ c • 1 := by decide

theorem witness_spec : ∀ g ∈ [gA, gB, gC], (g.map barF)ᵀ * g = 1 ∧ g.det = 1 ∧
    (∃ c : F9, c ^ 4 = 1 ∧ qOf g * qOf g = c • 1) ∧ ∀ c : F9, qOf g ≠ c • 1 := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨gA_unitary, gA_det, ⟨-1, by decide, qA_sq⟩, qA_ne⟩
  · exact ⟨gB_unitary, gB_det, ⟨1, by decide, qB_sq⟩, qB_ne⟩
  · exact ⟨gC_unitary, gC_det, ⟨1, by decide, qC_sq⟩, qC_ne⟩

@[expose] def f9List : List F9 :=
  [f9 0 0, f9 1 0, f9 2 0, f9 0 1, f9 1 1, f9 2 1, f9 0 2, f9 1 2, f9 2 2]

@[expose] def zv : V4 → V4
  | ⟨a, b, c, d⟩ =>
    ⟨f9 2 2 * b + f9 1 1 * d, f9 1 2 * b + f9 1 2 * d, f9 2 2 * a + f9 1 1 * c,
      f9 2 1 * a + f9 2 1 * c⟩

@[expose] def herm : V4 → V4 → F9
  | ⟨a, b, c, d⟩, ⟨a', b', c', d'⟩ => barF a * a' + barF b * b' + barF c * c' + barF d * d'

@[expose] def cond3 (v : V4) : Bool :=
  herm v v == 1 && (herm v (zv v) == 0 && herm v (zv (zv v)) == 1)

@[expose] def kryl4 (v : V4) : M4 :=
  match v, zv v, zv (zv v), zv (zv (zv v)) with
  | ⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩ =>
    ⟨a0, b0, c0, d0, a1, b1, c1, d1, a2, b2, c2, d2, a3, b3, c3, d3⟩

@[expose] def wits4 : List M4 := [gA4, gB4, gC4]

@[expose] def goodG (ψ : F9 → F9) (A : M4) : Bool :=
  wits4.any fun g => mu4.any fun lam => decide (A.mul (g.map ψ) = (g.mul A).smul lam)

@[expose] def e3t (ψ : F9 → F9) (A : M4) (v : V4) : Bool :=
  match A.mulV (v.map ψ) with
  | ⟨_, w1, w2, w3⟩ => w1 == 0 && w2 == 0 && w3 == 0

@[expose] def chkOne (ψ : F9 → F9) (K : M4) (v : V4) : Bool :=
  let A := (kryl4 v).mul K
  !e3t ψ A v || goodG ψ A

@[expose] def chk (v : V4) : Bool :=
  !cond3 v || (chkOne id kInvId4 v && chkOne barF kInvBar4 v)

@[expose] def chkAll : Bool :=
  f9List.all fun a => f9List.all fun b => f9List.all fun c => f9List.all fun d =>
    chk ⟨a, b, c, d⟩

theorem chkAll_eq : chkAll = true := by decide +kernel

theorem mem_f9List (x : F9) : x ∈ f9List := by
  revert x
  decide

theorem chk_eq (v : V4) : chk v = true := by
  have h := chkAll_eq
  unfold chkAll at h
  simp only [List.all_eq_true] at h
  rcases v with ⟨a, b, c, d⟩
  exact h a (mem_f9List a) b (mem_f9List b) c (mem_f9List c) d (mem_f9List d)

theorem M4.toMat_mul (A B : M4) : (A.mul B).toMat = A.toMat * B.toMat := by
  cases A; cases B
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [M4.mul, M4.toMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem M4.toMat_smul (c : F9) (A : M4) : (A.smul c).toMat = c • A.toMat := by
  cases A
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [M4.smul, M4.toMat]

theorem M4.toMat_map (ψ : F9 → F9) (A : M4) : (A.map ψ).toMat = A.toMat.map ψ := by
  cases A
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [M4.map, M4.toMat]

theorem M4.toMat_mulV (A : M4) (v : V4) : (A.mulV v).toVec = A.toMat *ᵥ v.toVec := by
  cases A; cases v
  refine funext fun i => ?_
  fin_cases i <;> simp [M4.mulV, M4.toMat, V4.toVec, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem V4.toVec_map (ψ : F9 → F9) (v : V4) : (v.map ψ).toVec = fun i => ψ (v.toVec i) := by
  cases v
  refine funext fun i => ?_
  fin_cases i <;> simp [V4.map, V4.toVec]

theorem V4.toVec_ofVec (u : Fin 4 → F9) : (V4.ofVec u).toVec = u := by
  refine funext fun i => ?_
  fin_cases i <;> rfl

theorem V4.ofVec_toVec (v : V4) : V4.ofVec v.toVec = v := by
  cases v
  rfl

@[simp] theorem V4.toVec_zero (v : V4) : v.toVec 0 = v.x0 := by cases v; rfl
@[simp] theorem V4.toVec_one (v : V4) : v.toVec 1 = v.x1 := by cases v; rfl
@[simp] theorem V4.toVec_two (v : V4) : v.toVec 2 = v.x2 := by cases v; rfl
@[simp] theorem V4.toVec_three (v : V4) : v.toVec 3 = v.x3 := by cases v; rfl

@[simp] theorem f9_zero : f9 0 0 = 0 := rfl

theorem zv_toVec (v : V4) : (zv v).toVec = zM *ᵥ v.toVec := by
  cases v
  refine funext fun i => ?_
  fin_cases i <;>
    simp [zv, zM, zM4, M4.toMat, V4.toVec, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem zv_ofVec (u : Fin 4 → F9) : zv (V4.ofVec u) = V4.ofVec (zM *ᵥ u) := by
  conv_lhs => rw [← V4.ofVec_toVec (zv (V4.ofVec u))]
  rw [zv_toVec, V4.toVec_ofVec]

@[expose] def kcol (Z : Matrix (Fin 4) (Fin 4) F9) (v : Fin 4 → F9) : ℕ → (Fin 4 → F9)
  | 0 => v
  | k + 1 => Z *ᵥ kcol Z v k

@[expose] def kryl (Z : Matrix (Fin 4) (Fin 4) F9) (v : Fin 4 → F9) : Matrix (Fin 4) (Fin 4) F9 :=
  Matrix.of fun i k => kcol Z v k i

theorem kryl4_eq (v : V4) : kryl4 v = ⟨v.x0, (zv v).x0, (zv (zv v)).x0, (zv (zv (zv v))).x0,
    v.x1, (zv v).x1, (zv (zv v)).x1, (zv (zv (zv v))).x1,
    v.x2, (zv v).x2, (zv (zv v)).x2, (zv (zv (zv v))).x2,
    v.x3, (zv v).x3, (zv (zv v)).x3, (zv (zv (zv v))).x3⟩ := by
  cases v
  rfl

theorem toMat_kryl4 (v : V4) : (kryl4 v).toMat = kryl zM v.toVec := by
  have h1 : zM *ᵥ v.toVec = (zv v).toVec := (zv_toVec v).symm
  have h2 : zM *ᵥ (zv v).toVec = (zv (zv v)).toVec := (zv_toVec _).symm
  have h3 : zM *ᵥ (zv (zv v)).toVec = (zv (zv (zv v))).toVec := (zv_toVec _).symm
  have e0 : kcol zM v.toVec 0 = v.toVec := rfl
  have e1' : kcol zM v.toVec 1 = (zv v).toVec := by simp [kcol, h1]
  have e2 : kcol zM v.toVec 2 = (zv (zv v)).toVec := by simp [kcol, h1, h2]
  have e3 : kcol zM v.toVec 3 = (zv (zv (zv v))).toVec := by simp [kcol, h1, h2, h3]
  refine Matrix.ext fun i k => ?_
  rw [kryl4_eq]
  fin_cases k <;> fin_cases i <;> simp [kryl, M4.toMat, e0, e1', e2, e3]

@[expose] def col0 (A : Matrix (Fin 4) (Fin 4) F9) : Fin 4 → F9 := fun i => A i 0

theorem col0_mul (M A : Matrix (Fin 4) (Fin 4) F9) : col0 (M * A) = M *ᵥ col0 A := by
  refine funext fun i => ?_
  simp [col0, Matrix.mul_apply, Matrix.mulVec, dotProduct]

@[expose] def e1 : Fin 4 → F9 := ![1, 0, 0, 0]

theorem mulVec_e1 (A : Matrix (Fin 4) (Fin 4) F9) : A *ᵥ e1 = col0 A := by
  refine funext fun i => ?_
  simp [col0, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem herm_entry (A B : Matrix (Fin 4) (Fin 4) F9) :
    ((A.map barF)ᵀ * B) 0 0 = herm (V4.ofVec (col0 A)) (V4.ofVec (col0 B)) := by
  simp [herm, V4.ofVec, col0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply,
    Matrix.map_apply]

theorem cond3_of (ψ : F9 →+* F9) (A : Matrix (Fin 4) (Fin 4) F9)
    (h1 : A * zM.map ψ = zM * A) (h2 : (A.map barF)ᵀ * A = 1) :
    cond3 (V4.ofVec (col0 A)) = true := by
  have hz1 : zv (V4.ofVec (col0 A)) = V4.ofVec (col0 (zM * A)) := by
    rw [zv_ofVec, col0_mul]
  have hz2 : zv (zv (V4.ofVec (col0 A))) = V4.ofVec (col0 (zM * (zM * A))) := by
    rw [hz1, zv_ofVec]
    simp only [col0_mul]
  have c0 : herm (V4.ofVec (col0 A)) (V4.ofVec (col0 A)) = 1 := by
    rw [← herm_entry, h2]
    rfl
  have c1 : herm (V4.ofVec (col0 A)) (zv (V4.ofVec (col0 A))) = 0 := by
    rw [hz1, ← herm_entry]
    have : (A.map barF)ᵀ * (zM * A) = zM.map ψ := by
      rw [← h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [this]
    simp only [Matrix.map_apply]
    rw [show zM 0 0 = 0 from rfl, map_zero]
  have c2 : herm (V4.ofVec (col0 A)) (zv (zv (V4.ofVec (col0 A)))) = 1 := by
    rw [hz2, ← herm_entry]
    have : (A.map barF)ᵀ * (zM * (zM * A)) = zM.map ψ * zM.map ψ := by
      rw [← h1, ← Matrix.mul_assoc zM, ← h1, Matrix.mul_assoc, ← Matrix.mul_assoc, h2,
        Matrix.one_mul]
    rw [this, ← Matrix.map_mul]
    have h11 : (zM * zM) 0 0 = 1 := by decide
    simp only [Matrix.map_apply]
    rw [h11, map_one]
  simp [cond3, c0, c1, c2]

theorem kcol_intertwine (A Zφ Z : Matrix (Fin 4) (Fin 4) F9) (h : A * Zφ = Z * A)
    (w : Fin 4 → F9) (k : ℕ) : A *ᵥ kcol Zφ w k = kcol Z (A *ᵥ w) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [kcol]
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, ih]

theorem mul_kryl (A Zφ Z : Matrix (Fin 4) (Fin 4) F9) (h : A * Zφ = Z * A) (w : Fin 4 → F9) :
    A * kryl Zφ w = kryl Z (A *ᵥ w) := by
  refine Matrix.ext fun i k => ?_
  have := congrFun (kcol_intertwine A Zφ Z h w k) i
  simpa [kryl, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem eq_kryl_mul (A Zφ : Matrix (Fin 4) (Fin 4) F9) (h : A * Zφ = zM * A)
    (K : Matrix (Fin 4) (Fin 4) F9) (hK : kryl Zφ e1 * K = 1) :
    A = kryl zM (A *ᵥ e1) * K := by
  calc A = A * (kryl Zφ e1 * K) := by rw [hK, Matrix.mul_one]
    _ = (A * kryl Zφ e1) * K := by rw [Matrix.mul_assoc]
    _ = kryl zM (A *ᵥ e1) * K := by rw [mul_kryl A Zφ zM h e1]

theorem e3_vec (ψ : F9 →+* F9) (A : Matrix (Fin 4) (Fin 4) F9) (c : F9)
    (h : A * A.map ψ = c • 1) : A *ᵥ (fun i => ψ (A i 0)) = c • e1 := by
  have h1 : (A * A.map ψ) *ᵥ e1 = c • e1 := by
    rw [h]
    refine funext fun i => ?_
    simp [Matrix.mulVec, dotProduct, e1, Matrix.smul_apply, Matrix.one_apply]
  rw [← Matrix.mulVec_mulVec] at h1
  have h2 : (A.map ψ) *ᵥ e1 = fun i => ψ (A i 0) := by
    refine funext fun i => ?_
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, e1]
  rwa [h2] at h1

theorem e3t_of (ψ : F9 → F9) (A : M4) (v : V4) (c : F9)
    (h : A.toMat *ᵥ (fun i => ψ (v.toVec i)) = c • e1) : e3t ψ A v = true := by
  unfold e3t
  rcases hA : A.mulV (v.map ψ) with ⟨w0, w1, w2, w3⟩
  have key : (A.mulV (v.map ψ)).toVec = c • e1 := by
    rw [M4.toMat_mulV, V4.toVec_map]
    exact h
  rw [hA] at key
  have k1 := congrFun key 1
  have k2 := congrFun key 2
  have k3 := congrFun key 3
  simp [V4.toVec, e1] at k1 k2 k3
  simp [k1, k2, k3]

theorem goodG_spec (ψ : F9 → F9) (A : M4) (h : goodG ψ A = true) :
    ∃ g ∈ [gA, gB, gC], ∃ lam ∈ mu4, A.toMat * g.map ψ = lam • (g * A.toMat) := by
  unfold goodG at h
  simp only [List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨g4, hg4, lam, hlam, heq⟩ := h
  have := congrArg M4.toMat heq
  rw [M4.toMat_mul, M4.toMat_smul, M4.toMat_mul, M4.toMat_map] at this
  refine ⟨g4.toMat, ?_, lam, hlam, this⟩
  simp only [wits4, List.mem_cons, List.not_mem_nil, or_false] at hg4
  rcases hg4 with rfl | rfl | rfl <;> simp [gA, gB, gC]

theorem finite_core (ψ : F9 →+* F9) (K4 : M4) (hK : kryl (zM.map ψ) e1 * K4.toMat = 1)
    (hchk : ∀ v : V4, cond3 v = true → chkOne ψ K4 v = true)
    (A : Matrix (Fin 4) (Fin 4) F9) (h1 : A * zM.map ψ = zM * A)
    (h2 : (A.map barF)ᵀ * A = 1) (h3 : ∃ c : F9, A * A.map ψ = c • 1) :
    ∃ g ∈ [gA, gB, gC], ∃ lam ∈ mu4, A * g.map ψ = lam • (g * A) := by
  obtain ⟨c, hc⟩ := h3
  set v : V4 := V4.ofVec (col0 A) with hv
  have hvec : v.toVec = col0 A := V4.toVec_ofVec _
  have hA : A = (M4.mul (kryl4 v) K4).toMat := by
    rw [M4.toMat_mul, toMat_kryl4, hvec, ← mulVec_e1]
    exact eq_kryl_mul A _ h1 K4.toMat hK
  have hc3 : cond3 v = true := cond3_of ψ A h1 h2
  have hone := hchk v hc3
  have he3 : e3t ψ (M4.mul (kryl4 v) K4) v = true := by
    refine e3t_of ψ _ v c ?_
    rw [← hA, hvec]
    exact e3_vec ψ A c hc
  have hgood : goodG ψ (M4.mul (kryl4 v) K4) = true := by
    unfold chkOne at hone
    simpa [he3] using hone
  obtain ⟨g, hg, lam, hlam, heq⟩ := goodG_spec ψ _ hgood
  rw [← hA] at heq
  exact ⟨g, hg, lam, hlam, heq⟩

theorem kryl_id : kryl zM e1 * kInvId4.toMat = 1 := by decide

theorem kryl_bar : kryl (zM.map barF) e1 * kInvBar4.toMat = 1 := by decide

theorem finite_id (ψ : F9 →+* F9) (hψ : ∀ x, ψ x = x)
    (A : Matrix (Fin 4) (Fin 4) F9) (h1 : A * zM.map ψ = zM * A)
    (h2 : (A.map barF)ᵀ * A = 1) (h3 : ∃ c : F9, A * A.map ψ = c • 1) :
    ∃ g ∈ [gA, gB, gC], ∃ lam ∈ mu4, A * g.map ψ = lam • (g * A) := by
  have hψ' : (⇑ψ : F9 → F9) = id := funext hψ
  refine finite_core ψ kInvId4 ?_ ?_ A h1 h2 h3
  · have : zM.map ψ = zM := by
      refine Matrix.ext fun i j => ?_
      simp [hψ]
    rw [this]
    exact kryl_id
  · intro v hv
    have := chk_eq v
    simp only [chk, hv, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    rw [hψ']
    exact this.1

theorem finite_bar (ψ : F9 →+* F9) (hψ : ∀ x, ψ x = barF x)
    (A : Matrix (Fin 4) (Fin 4) F9) (h1 : A * zM.map ψ = zM * A)
    (h2 : (A.map barF)ᵀ * A = 1) (h3 : ∃ c : F9, A * A.map ψ = c • 1) :
    ∃ g ∈ [gA, gB, gC], ∃ lam ∈ mu4, A * g.map ψ = lam • (g * A) := by
  have hψ' : (⇑ψ : F9 → F9) = barF := funext hψ
  refine finite_core ψ kInvBar4 ?_ ?_ A h1 h2 h3
  · have : zM.map ψ = zM.map barF := by
      refine Matrix.ext fun i j => ?_
      simp [hψ]
    rw [this]
    exact kryl_bar
  · intro v hv
    have := chk_eq v
    simp only [chk, hv, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    rw [hψ']
    exact this.2

end CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat
