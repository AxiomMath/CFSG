module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.S45.LEvSporCorr
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Matrix

section Signs

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem mul_pow_comm_sign {A B : Matrix ι ι F} {s : F} (h : A * B = s • (B * A)) (n : ℕ) :
    A * B ^ n = s ^ n • (B ^ n * A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc A * B ^ (n + 1) = A * B ^ n * B := by rw [pow_succ, Matrix.mul_assoc]
      _ = s ^ n • (B ^ n * A) * B := by rw [ih]
      _ = s ^ n • (B ^ n * (A * B)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = s ^ n • (B ^ n * (s • (B * A))) := by rw [h]
      _ = s ^ (n + 1) • (B ^ (n + 1) * A) := by
        rw [Matrix.mul_smul, smul_smul, ← pow_succ, pow_succ B n, Matrix.mul_assoc]

omit [DecidableEq ι] in
theorem mul_mul_comm_sign {A X Y : Matrix ι ι F} {s t : F} (hX : A * X = s • (X * A))
    (hY : A * Y = t • (Y * A)) : A * (X * Y) = (s * t) • ((X * Y) * A) := by
  calc A * (X * Y) = (A * X) * Y := (Matrix.mul_assoc _ _ _).symm
    _ = (s • (X * A)) * Y := by rw [hX]
    _ = s • (X * (A * Y)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
    _ = s • (X * (t • (Y * A))) := by rw [hY]
    _ = (s * t) • (X * (Y * A)) := by rw [Matrix.mul_smul, smul_smul]
    _ = (s * t) • ((X * Y) * A) := by rw [← Matrix.mul_assoc]

omit [DecidableEq ι] in
theorem mul_prod_four_comm_sign {A X₀ X₁ X₂ X₃ : Matrix ι ι F} {s₀ s₁ s₂ s₃ : F}
    (h₀ : A * X₀ = s₀ • (X₀ * A)) (h₁ : A * X₁ = s₁ • (X₁ * A)) (h₂ : A * X₂ = s₂ • (X₂ * A))
    (h₃ : A * X₃ = s₃ • (X₃ * A)) :
    A * (X₀ * (X₁ * (X₂ * X₃))) = (s₀ * (s₁ * (s₂ * s₃))) • ((X₀ * (X₁ * (X₂ * X₃))) * A) :=
  mul_mul_comm_sign h₀ (mul_mul_comm_sign h₁ (mul_mul_comm_sign h₂ h₃))

theorem not_scalar_of_comm_signs [Nonempty ι] (hF : (-1 : F) ≠ 1) (g : Fin 4 → GL ι F)
    (w : Fin 4 → Fin 4 → ℕ)
    (hw : ∀ i j, (g i : Matrix ι ι F) * (g j : Matrix ι ι F) =
      (-1 : F) ^ w i j • ((g j : Matrix ι ι F) * (g i : Matrix ι ι F)))
    (hnd : ∀ a : Fin 4 → Fin 2, a ≠ 0 → ∃ j, ¬ 2 ∣ ∑ i, w j i * (a i : ℕ)) :
    ∀ a : Fin 4 → Fin 2, a ≠ 0 → ∀ c : F,
      ((List.ofFn fun i => g i ^ (a i : ℕ)).prod : Matrix ι ι F) ≠ c • (1 : Matrix ι ι F) := by
  intro a ha c hM
  obtain ⟨j, hj⟩ := hnd a ha
  have hexp : ((List.ofFn fun i => g i ^ (a i : ℕ)).prod : Matrix ι ι F) =
      (g 0 : Matrix ι ι F) ^ (a 0 : ℕ) * ((g 1 : Matrix ι ι F) ^ (a 1 : ℕ) *
        ((g 2 : Matrix ι ι F) ^ (a 2 : ℕ) * (g 3 : Matrix ι ι F) ^ (a 3 : ℕ))) := by
    simp [List.ofFn_succ, Units.val_pow_eq_pow_val]
  have hprod := mul_prod_four_comm_sign (A := (g j : Matrix ι ι F))
    (mul_pow_comm_sign (hw j 0) (a 0 : ℕ)) (mul_pow_comm_sign (hw j 1) (a 1 : ℕ))
    (mul_pow_comm_sign (hw j 2) (a 2 : ℕ)) (mul_pow_comm_sign (hw j 3) (a 3 : ℕ))
  have hsc : ((-1 : F) ^ w j 0) ^ (a 0 : ℕ) * (((-1 : F) ^ w j 1) ^ (a 1 : ℕ) *
      (((-1 : F) ^ w j 2) ^ (a 2 : ℕ) * ((-1 : F) ^ w j 3) ^ (a 3 : ℕ))) =
      (-1 : F) ^ (∑ i, w j i * (a i : ℕ)) := by
    simp only [Fin.sum_univ_four, pow_add, ← pow_mul, mul_assoc]
  rw [hsc, ← hexp, hM] at hprod
  have hodd : Odd (∑ i, w j i * (a i : ℕ)) := Nat.not_even_iff_odd.1 (by
    rwa [even_iff_two_dvd])
  rw [hodd.neg_one_pow, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    neg_smul, one_smul] at hprod
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h2 : (2 : F) ≠ 0 := fun h => hF (by linear_combination (-1 : F) * h)
  have hc : c = 0 := by
    have h1 := congrArg (fun X => X * ((g j)⁻¹ : GL ι F).val) hprod
    simp only [Matrix.smul_mul, Units.mul_inv, Matrix.neg_mul] at h1
    have h3 := congrFun (congrFun h1 i) i
    simp at h3
    have h4 : 2 * c = 0 := by linear_combination h3
    exact (mul_eq_zero.1 h4).resolve_left h2
  set U : GL ι F := (List.ofFn fun i => g i ^ (a i : ℕ)).prod with hU
  have h5 : (U : Matrix ι ι F) * ((U⁻¹ : GL ι F) : Matrix ι ι F) = 1 := Units.mul_inv U
  rw [hM, hc, zero_smul, zero_mul] at h5
  have h6 := congrFun (congrFun h5 i) i
  simp at h6

end Signs

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
