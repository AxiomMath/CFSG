module

public import CFSG.LieType.SeitzGeneration.NonabLift
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeTrans

public section

namespace CFSG.LieType.SeitzGeneration

open Module Matrix
open scoped commutatorElement

variable {F : Type*} [Field F]

theorem fin_three_cayley_hamilton (M : Matrix (Fin 3) (Fin 3) F) :
    M ^ 3 = M.trace • M ^ 2 - M.adjugate.trace • M + M.det • (1 : Matrix (Fin 3) (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three,
      Matrix.adjugate_fin_three, Matrix.det_fin_three] <;> ring

theorem trace_eq_zero_of_quasi_commute {n : Type*} [Fintype n] [DecidableEq n]
    {A B B' : Matrix n n F} {ζ : F} (hζ : ζ ≠ 1) (hB : B' * B = 1) (hB' : B * B' = 1)
    (h : B * A = ζ • (A * B)) : A.trace = 0 := by
  have h1 : A.trace = ζ * A.trace := by
    calc A.trace = (B' * (B * A)).trace := by rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
      _ = (B' * (ζ • (A * B))).trace := by rw [h]
      _ = ζ * (B' * A * B).trace := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
      _ = ζ * (B * B' * A).trace := by rw [Matrix.trace_mul_cycle]
      _ = ζ * A.trace := by rw [hB', Matrix.one_mul]
  have h2 : (1 - ζ) * A.trace = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hζ))

theorem matrix_eq_of_mulVec_single {M N : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ j, M.mulVec (Pi.single j 1) = N.mulVec (Pi.single j 1)) : M = N := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h j) i

theorem exists_heisenberg_basis {x y : SpecialLinearGroup (Fin 3) F}
    (hyx : ⁅y, x⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F)) (hne : x * y ≠ y * x)
    (hx3 : x ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F)) :
    ∃ (P : GL (Fin 3) F) (ω ξ : F) (hξ : ξ * (ξ * ω) * (ξ * ω ^ 2) = 1),
      ω ^ 2 + ω + 1 = 0 ∧ ω ≠ 1 ∧ conjUnit P⁻¹ y = diagSL ξ (ξ * ω) (ξ * ω ^ 2) hξ ∧
        conjUnit P⁻¹ x = shiftSL := by
  classical
  set X : Matrix (Fin 3) (Fin 3) F := (x : Matrix (Fin 3) (Fin 3) F) with hX
  set Y : Matrix (Fin 3) (Fin 3) F := (y : Matrix (Fin 3) (Fin 3) F) with hY
  obtain ⟨ω, hω0, hω⟩ := exists_scalar_of_mem_center (n := 3) (by norm_num) hyx
  have hω1 : ω ≠ 1 := by
    intro h
    apply hne
    have h1 : ⁅y, x⁆ = 1 := Subtype.ext (by rw [hω, h, one_smul]; rfl)
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hω3 : ω ^ 3 = 1 := by
    have h1 := (⁅y, x⁆ : SpecialLinearGroup (Fin 3) F).2
    rw [hω, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact h1
  have hωq : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω1)
  have hrel : Y * X = ω • (X * Y) := by
    have h1 : (⁅y, x⁆ : SpecialLinearGroup (Fin 3) F) * (x * y) = y * x := by
      simp only [commutatorElement_def]; group
    have h2 := congrArg Subtype.val h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hω,
      Matrix.smul_mul, Matrix.one_mul] at h2
    exact h2.symm
  set W : Matrix (Fin 3) (Fin 3) F := ((y⁻¹ : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hW
  set X' : Matrix (Fin 3) (Fin 3) F := ((x⁻¹ : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hX'
  have hYW : Y * W = 1 := by
    have h1 := congrArg Subtype.val (mul_inv_cancel y)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  have hWY : W * Y = 1 := by
    have h1 := congrArg Subtype.val (inv_mul_cancel y)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  have hXX' : X * X' = 1 := by
    have h1 := congrArg Subtype.val (mul_inv_cancel x)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  have hX'X : X' * X = 1 := by
    have h1 := congrArg Subtype.val (inv_mul_cancel x)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  have hrelinv : X * Y = ω⁻¹ • (Y * X) := by
    rw [hrel, smul_smul, inv_mul_cancel₀ hω0, one_smul]
  have htY : Y.trace = 0 :=
    trace_eq_zero_of_quasi_commute (A := Y) (B := X) (B' := X') (ζ := ω⁻¹)
      (fun h => hω1 (inv_eq_one.1 h)) hX'X hXX' hrelinv
  have hrelW : X * W = ω • (W * X) := by
    have h1 : W * (Y * X) * W = W * (ω • (X * Y)) * W := by rw [hrel]
    have e1 : W * (Y * X) * W = X * W := by
      calc W * (Y * X) * W = (W * Y) * X * W := by simp only [Matrix.mul_assoc]
        _ = X * W := by rw [hWY, Matrix.one_mul]
    have e2 : W * (ω • (X * Y)) * W = ω • (W * X) := by
      calc W * (ω • (X * Y)) * W = ω • (W * X * (Y * W)) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
        _ = ω • (W * X) := by rw [hYW, Matrix.mul_one]
    rw [← e1, h1, e2]
  have htW : W.trace = 0 :=
    trace_eq_zero_of_quasi_commute (A := W) (B := X) (B' := X') hω1 hX'X hXX' hrelW
  have hY3 : Y ^ 3 = 1 := by
    have hadj : Y.adjugate = W := (Matrix.SpecialLinearGroup.coe_inv y).symm
    have hdet : Y.det = 1 := y.2
    rw [fin_three_cayley_hamilton Y, hadj, htY, htW, hdet]
    simp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprim : IsPrimitiveRoot ω 3 := by
    have h1 := orderOf_eq_prime hω3 hω1
    rw [← h1]
    exact IsPrimitiveRoot.orderOf ω
  obtain ⟨ξ, v, hξ3, hv0, hYv⟩ :=
    exists_eigenvector_of_pow_eq_one (p := 3) (by norm_num) ⟨ω, hprim⟩ (by norm_num) hY3
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  have hYX : ∀ k : ℕ, Y * X ^ k = ω ^ k • (X ^ k * Y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc Y * X ^ (k + 1) = (Y * X ^ k) * X := by rw [pow_succ, Matrix.mul_assoc]
        _ = ω ^ k • (X ^ k * (Y * X)) := by
          rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
        _ = ω ^ (k + 1) • (X ^ (k + 1) * Y) := by
          rw [hrel, Matrix.mul_smul, smul_smul, pow_succ ω k, pow_succ X k, mul_comm (ω ^ k) ω,
            Matrix.mul_assoc]
  let u : Fin 3 → (Fin 3 → F) := fun k => (X ^ (k : ℕ)).mulVec v
  have hYu : ∀ k : Fin 3, Y.mulVec (u k) = (ω ^ (k : ℕ) * ξ) • u k := by
    intro k
    simp only [u]
    rw [Matrix.mulVec_mulVec, hYX, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_smul, smul_smul]
  have hu0 : ∀ k : Fin 3, u k ≠ 0 := by
    intro k hk
    have hdet : (X ^ (k : ℕ)).det = 1 := by
      have h1 := (x ^ (k : ℕ)).2
      rwa [Matrix.SpecialLinearGroup.coe_pow] at h1
    have h1 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hk⟩
    rw [hdet] at h1
    exact one_ne_zero h1
  have hinj : Function.Injective (fun k : Fin 3 => ω ^ (k : ℕ) * ξ) := by
    intro k l h
    have h' : ω ^ (k : ℕ) = ω ^ (l : ℕ) := mul_right_cancel₀ hξ0 h
    exact Fin.ext (hprim.pow_inj k.2 l.2 h')
  have hli : LinearIndependent F u :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' Y)
      (fun k : Fin 3 => ω ^ (k : ℕ) * ξ) hinj u
      (fun k => ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hYu k, hu0 k⟩)
  let b : Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank' u hli (by simp)
  have hb : ∀ k, b k = u k := fun k => by simp [b]
  set P : GL (Fin 3) F := basisUnit b with hP
  have hconj : ∀ (g : SpecialLinearGroup (Fin 3) F) (j : Fin 3),
      ((conjUnit P⁻¹ g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Pi.single j 1) = ⇑(b.repr ((g : Matrix (Fin 3) (Fin 3) F).mulVec (b j))) := by
    intro g j
    rw [conjUnit_coe, inv_inv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP,
      basisUnit_mulVec_single, one_smul, basisUnit_inv_mulVec]
  have hcolY : ∀ j : Fin 3,
      ((conjUnit P⁻¹ y : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Pi.single j 1) = (ω ^ (j : ℕ) * ξ) • Pi.single j 1 := by
    intro j
    rw [hconj, hb j, hYu j, ← hb j, map_smul, Basis.repr_self]
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hξ' : ξ * (ξ * ω) * (ξ * ω ^ 2) = 1 := by linear_combination ω ^ 3 * hξ3 + hω3
  have hconjY : conjUnit P⁻¹ y = diagSL ξ (ξ * ω) (ξ * ω ^ 2) hξ' := by
    apply Subtype.ext
    apply matrix_eq_of_mulVec_single
    intro j
    rw [hcolY j]
    ext i
    fin_cases i <;> fin_cases j <;>
      simp [diagSL, mul_comm]
  obtain ⟨β, hβ0, hβ⟩ := exists_scalar_of_mem_center (n := 3) (by norm_num) hx3
  have hX3 : X ^ 3 = β • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [hX, ← Matrix.SpecialLinearGroup.coe_pow]; exact hβ
  have hu0' : u 0 = v := by simp [u]
  have hu1' : u 1 = X.mulVec v := by simp [u]
  have hu2' : u 2 = (X ^ 2).mulVec v := by simp [u]
  have hXu0 : X.mulVec (u 0) = u 1 := by rw [hu0', hu1']
  have hXu1 : X.mulVec (u 1) = u 2 := by
    rw [hu1', hu2', Matrix.mulVec_mulVec, pow_two]
  have hXu2 : X.mulVec (u 2) = β • u 0 := by
    have h1 : X * X ^ 2 = X ^ 3 := by rw [← pow_succ']
    rw [hu2', Matrix.mulVec_mulVec, h1, hX3, Matrix.smul_mulVec, Matrix.one_mulVec, hu0']
  have hcolX : ∀ j : Fin 3,
      ((conjUnit P⁻¹ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Pi.single j 1) = (!![0, 0, β; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).mulVec
          (Pi.single j 1) := by
    intro j
    rw [hconj, hb j, ← hX]
    fin_cases j
    · simp only [Fin.zero_eta]
      rw [hXu0, ← hb 1, Basis.repr_self]
      ext i
      fin_cases i <;> simp
    · simp only [Fin.mk_one]
      rw [hXu1, ← hb 2, Basis.repr_self]
      ext i
      fin_cases i <;> simp
    · simp only [Fin.reduceFinMk]
      rw [hXu2, ← hb 0, map_smul, Basis.repr_self]
      ext i
      fin_cases i <;> simp
  have hmatX : ((conjUnit P⁻¹ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, β; 1, 0, 0; 0, 1, 0] := matrix_eq_of_mulVec_single hcolX
  have hβ1 : β = 1 := by
    have h1 := (conjUnit P⁻¹ x).2
    rw [hmatX] at h1
    simpa [Matrix.det_fin_three] using h1
  refine ⟨P, ω, ξ, hξ', hωq, hω1, hconjY, Subtype.ext ?_⟩
  rw [hmatX, hβ1]
  rfl

end CFSG.LieType.SeitzGeneration
