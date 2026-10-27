module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CFSG.Certificates.Kernel.BabyMonster.DyLaneSpr

public section

namespace CFSG.KC.BM.Ln

open scoped Matrix

set_option linter.unusedSectionVars false

variable {n : Type} [Fintype n] [DecidableEq n]

@[expose] def IntRep (A : Matrix n n ℚ) (S : Matrix n n (ZMod 2)) : Prop :=
  ∃ Z : Matrix n n ℤ, A = Z.map (Int.castRingHom ℚ) ∧ Z.map (Int.castRingHom (ZMod 2)) = S

theorem IntRep.mul {A A' : Matrix n n ℚ} {S S' : Matrix n n (ZMod 2)} (h : IntRep A S)
    (h' : IntRep A' S') : IntRep (A * A') (S * S') := by
  obtain ⟨Z, rfl, rfl⟩ := h
  obtain ⟨Z', rfl, rfl⟩ := h'
  exact ⟨Z * Z', (Matrix.map_mul).symm, Matrix.map_mul⟩

theorem IntRep.one : IntRep (1 : Matrix n n ℚ) 1 :=
  ⟨1, (Matrix.map_one _ (map_zero _) (map_one _)).symm, Matrix.map_one _ (map_zero _) (map_one _)⟩

theorem IntRep.pow {A : Matrix n n ℚ} {S : Matrix n n (ZMod 2)} (h : IntRep A S) :
    ∀ k : ℕ, IntRep (A ^ k) (S ^ k)
  | 0 => by rw [pow_zero, pow_zero]; exact IntRep.one
  | k + 1 => by rw [pow_succ, pow_succ]; exact (h.pow k).mul h

theorem IntRep.unique {A : Matrix n n ℚ} {S S' : Matrix n n (ZMod 2)} (h : IntRep A S)
    (h' : IntRep A S') : S = S' := by
  obtain ⟨Z, hZ, rfl⟩ := h
  obtain ⟨Z', hZ', rfl⟩ := h'
  have : Z = Z' := by
    ext i j
    have := congrFun (congrFun (hZ.symm.trans hZ') i) j
    simp only [Matrix.map_apply, eq_intCast, Int.cast_inj] at this
    exact this
  rw [this]

theorem IntRep.congr {A A' : Matrix n n ℚ} {S S' : Matrix n n (ZMod 2)} (h : IntRep A S) (hA : A = A')
    (hS : S = S') : IntRep A' S' := hA ▸ hS ▸ h

@[expose] noncomputable def Cn (B M : Matrix n n ℚ) : Matrix n n ℚ := B * M * B⁻¹

theorem Cn_mul {B : Matrix n n ℚ} (hB : IsUnit B.det) (M N : Matrix n n ℚ) :
    Cn B (M * N) = Cn B M * Cn B N := by
  unfold Cn
  rw [show B * M * B⁻¹ * (B * N * B⁻¹) = B * M * (B⁻¹ * B) * N * B⁻¹ by
    simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul B hB, Matrix.mul_one, Matrix.mul_assoc B M N]

theorem Cn_one {B : Matrix n n ℚ} (hB : IsUnit B.det) : Cn B 1 = 1 := by
  unfold Cn
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv B hB]

theorem Cn_pow {B : Matrix n n ℚ} (hB : IsUnit B.det) (M : Matrix n n ℚ) :
    ∀ k : ℕ, Cn B (M ^ k) = Cn B M ^ k
  | 0 => by rw [pow_zero, pow_zero, Cn_one hB]
  | k + 1 => by rw [pow_succ, pow_succ, Cn_mul hB, Cn_pow hB M k]

theorem Cn_prod {B : Matrix n n ℚ} (hB : IsUnit B.det) :
    ∀ L : List (Matrix n n ℚ), Cn B L.prod = (L.map (Cn B)).prod
  | [] => by rw [List.prod_nil, List.map_nil, List.prod_nil, Cn_one hB]
  | M :: L => by rw [List.prod_cons, Cn_mul hB, Cn_prod hB L, List.map_cons, List.prod_cons]

theorem SU_pow {B U : Matrix n n ℚ} (hB : IsUnit B.det) {k : ℕ} (hU : U ^ k = 1)
    {SU : Matrix n n (ZMod 2)} (hCU : IntRep (Cn B U) SU) : SU ^ k = 1 := by
  have h1 := hCU.pow k
  rw [← Cn_pow hB, hU, Cn_one hB] at h1
  exact h1.unique IntRep.one

theorem transfer_x {B My Mx U : Matrix n n ℚ} (hB : IsUnit B.det) (hrel : My * U = U * Mx) {k : ℕ}
    (hk : 1 ≤ k) (hU : U ^ k = 1) {SU Sy Sx : Matrix n n (ZMod 2)} (hCU : IntRep (Cn B U) SU)
    (hy : IntRep (Cn B My) Sy) (hS : Sy * SU = SU * Sx) : IntRep (Cn B Mx) Sx := by
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hMx : Mx = U ^ (k - 1) * My * U := by
    rw [Matrix.mul_assoc, hrel, ← Matrix.mul_assoc, ← pow_succ, hk', hU, Matrix.one_mul]
  have hSU := SU_pow hB hU hCU
  refine ((hCU.pow (k - 1)).mul hy |>.mul hCU).congr ?_ ?_
  · rw [hMx, Cn_mul hB, Cn_mul hB, Cn_pow hB]
  · rw [Matrix.mul_assoc, hS, ← Matrix.mul_assoc, ← pow_succ, hk', hSU, Matrix.one_mul]

theorem transfer_y {B My Mx U : Matrix n n ℚ} (hB : IsUnit B.det) (hrel : My * U = U * Mx) {k : ℕ}
    (hk : 1 ≤ k) (hU : U ^ k = 1) {SU Sy Sx : Matrix n n (ZMod 2)} (hCU : IntRep (Cn B U) SU)
    (hx : IntRep (Cn B Mx) Sx) (hS : Sy * SU = SU * Sx) : IntRep (Cn B My) Sy := by
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hMy : My = U * Mx * U ^ (k - 1) := by
    rw [← hrel, Matrix.mul_assoc, ← pow_succ', hk', hU, Matrix.mul_one]
  have hSU := SU_pow hB hU hCU
  refine ((hCU.mul hx).mul (hCU.pow (k - 1))).congr ?_ ?_
  · rw [hMy, Cn_mul hB, Cn_mul hB, Cn_pow hB]
  · rw [← hS, Matrix.mul_assoc, ← pow_succ', hk', hSU, Matrix.mul_one]

end CFSG.KC.BM.Ln

end
