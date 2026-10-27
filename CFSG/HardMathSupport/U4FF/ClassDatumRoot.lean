module

public import CFSG.HardMathSupport.U4FF.ClassDatumDefs

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

namespace Datum

section Matrices

variable {K : Type} [Field K]

@[expose] def x0Mat (n : ℕ) (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, c, 0, 0; 0, 1, 0, 0; 0, 0, 1, c ^ 2 ^ n; 0, 0, 0, 1]

@[expose] def x1Mat (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, c, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def y0Mat (n : ℕ) (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; c, 1, 0, 0; 0, 0, 1, 0; 0, 0, c ^ 2 ^ n, 1]

@[expose] def y1Mat (c : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, c, 1, 0; 0, 0, 0, 1]

theorem isUpperUni_x0Mat (n : ℕ) (c : K) : IsUpperUni (x0Mat n c) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hji (by decide) | simp [x0Mat]
  · fin_cases i <;> simp [x0Mat]

theorem isUpperUni_x1Mat (c : K) : IsUpperUni (x1Mat c) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hji (by decide) | simp [x1Mat]
  · fin_cases i <;> simp [x1Mat]

theorem isLowerUni_y0Mat (n : ℕ) (c : K) : IsLowerUni (y0Mat n c) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [y0Mat]
  · fin_cases i <;> simp [y0Mat]

theorem isLowerUni_y1Mat (c : K) : IsLowerUni (y1Mat c) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [y1Mat]
  · fin_cases i <;> simp [y1Mat]

variable [CharP K 2]

theorem x0Mat_zero (n : ℕ) : (x0Mat n (0 : K)) = 1 := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x0Mat, zero_pow hq]

theorem x1Mat_zero : (x1Mat (0 : K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x1Mat]

theorem x0Mat_mul (n : ℕ) (c d : K) : x0Mat n c * x0Mat n d = x0Mat n (c + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x0Mat, Matrix.mul_apply, Fin.sum_univ_four, add_pow_char_pow] <;> ring

theorem x1Mat_mul (c d : K) : x1Mat c * x1Mat d = x1Mat (c + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x1Mat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end Matrices

section Entries

variable {K : Type} [Field K]

theorem upper_mul_01 {A B : Matrix (Fin 4) (Fin 4) K} (hA : IsUpperUni A) (hB : IsUpperUni B) :
    (A * B) 0 1 = A 0 1 + B 0 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four, hA.2 0, hB.2 1, hB.1 2 1 (by decide),
    hB.1 3 1 (by decide)]
  ring

theorem upper_mul_12 {A B : Matrix (Fin 4) (Fin 4) K} (hA : IsUpperUni A) (hB : IsUpperUni B) :
    (A * B) 1 2 = A 1 2 + B 1 2 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four, hA.1 1 0 (by decide), hA.2 1, hB.2 2,
    hB.1 3 2 (by decide)]
  ring

theorem upper_mul_23 {A B : Matrix (Fin 4) (Fin 4) K} (hA : IsUpperUni A) (hB : IsUpperUni B) :
    (A * B) 2 3 = A 2 3 + B 2 3 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four, hA.1 2 0 (by decide), hA.1 2 1 (by decide), hA.2 2,
    hB.2 3]
  ring

end Entries

section Elements

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)

theorem ucond_a (a : K) : UCond n a 0 0 0 := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  simp [UCond, zero_pow hq]

theorem ucond_c {c : K} (hc : c ^ 2 ^ n = c) : UCond n 0 0 c 0 := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  simp [UCond, zero_pow hq, hc]

@[expose] noncomputable def x0 (c : K) : G4 K n :=
  ⟨Matrix.SpecialLinearGroup.toGL (wSL n (c ^ 2 ^ n) 0 0 0), wMat_mem_SU n hK (ucond_a _)⟩

@[expose] noncomputable def x1 (c : Fq K n) : G4 K n :=
  ⟨Matrix.SpecialLinearGroup.toGL (wSL n 0 0 (c : K) 0), wMat_mem_SU n hK (ucond_c c.2)⟩

@[expose] noncomputable def y0 (c : K) : G4 K n :=
  ⟨Matrix.SpecialLinearGroup.toGL (uSL n c 0 0 0), uMat_mem_SU n hK (ucond_a _)⟩

@[expose] noncomputable def y1 (c : Fq K n) : G4 K n :=
  ⟨Matrix.SpecialLinearGroup.toGL (uSL n 0 0 (c : K) 0), uMat_mem_SU n hK (ucond_c c.2)⟩

theorem gm_x0 (c : K) : gm (x0 hK c) = x0Mat n c := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  show wMat n (c ^ 2 ^ n) 0 0 0 = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, x0Mat, pow_pow_of_card hK, zero_pow hq]

theorem gm_x1 (c : Fq K n) : gm (x1 hK c) = x1Mat (c : K) := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  show wMat n 0 0 (c : K) 0 = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, x1Mat, zero_pow hq]

theorem gm_y0 (c : K) : gm (y0 hK c) = y0Mat n c := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  show uMat n c 0 0 0 = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, y0Mat, zero_pow hq]

theorem gm_y1 (c : Fq K n) : gm (y1 hK c) = y1Mat (c : K) := by
  have hq : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  show uMat n 0 0 (c : K) 0 = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, y1Mat, zero_pow hq]

end Elements

section Membership

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem mem_UpperU' {g : G4 K n} : g ∈ UpperU K n ↔ IsUpperUni (gm g) := mem_UpperU

theorem mem_LowerU' {g : G4 K n} : g ∈ LowerU K n ↔ IsLowerUni (gm g) := mem_LowerU

end Membership

section RootGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def famSubgroup {n : ℕ} (f : K → Matrix (Fin 4) (Fin 4) K) (P : K → Prop) (hP0 : P 0)
    (hPadd : ∀ c d, P c → P d → P (c + d)) (hf0 : f 0 = 1)
    (hfmul : ∀ c d, f c * f d = f (c + d)) : Subgroup (G4 K n) where
  carrier := {g | ∃ c, P c ∧ gm g = f c}
  one_mem' := ⟨0, hP0, by rw [gm_one, hf0]⟩
  mul_mem' := by
    rintro g h ⟨c, hc, hg⟩ ⟨d, hd, hh⟩
    exact ⟨c + d, hPadd c d hc hd, by rw [gm_mul, hg, hh, hfmul]⟩
  inv_mem' := by
    rintro g ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    have h : gm g * gm g = 1 := by
      rw [hg, hfmul, CharTwo.add_self_eq_zero, hf0]
    exact (gm_inv_eq_of_sq h).trans hg

@[expose] def X0 (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Subgroup (G4 K n) :=
  famSubgroup (x0Mat n) (fun _ => True) trivial (fun _ _ _ _ => trivial) (x0Mat_zero n)
    (x0Mat_mul n)

@[expose] def X1 (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Subgroup (G4 K n) :=
  famSubgroup x1Mat (fun c => c ^ 2 ^ n = c)
    (by simp [zero_pow (pow_ne_zero n two_ne_zero)])
    (fun c d hc hd => by rw [add_pow_char_pow, hc, hd]) x1Mat_zero x1Mat_mul

theorem mem_X0 {n : ℕ} {g : G4 K n} : g ∈ X0 K n ↔ ∃ c : K, gm g = x0Mat n c :=
  ⟨fun ⟨c, _, h⟩ => ⟨c, h⟩, fun ⟨c, h⟩ => ⟨c, trivial, h⟩⟩

theorem mem_X1 {n : ℕ} {g : G4 K n} :
    g ∈ X1 K n ↔ ∃ c : K, c ^ 2 ^ n = c ∧ gm g = x1Mat c :=
  Iff.rfl

theorem x0_mem_X0 {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (c : K) : x0 hK c ∈ X0 K n :=
  mem_X0.mpr ⟨c, gm_x0 hK c⟩

theorem x1_mem_X1 {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (c : Fq K n) : x1 hK c ∈ X1 K n :=
  mem_X1.mpr ⟨c, c.2, gm_x1 hK c⟩

theorem X0_le_U (n : ℕ) : X0 K n ≤ UpperU K n := by
  intro g hg
  obtain ⟨c, hc⟩ := mem_X0.mp hg
  have h : IsUpperUni (gm g) := by
    rw [hc]
    exact isUpperUni_x0Mat n c
  exact mem_UpperU'.mpr h

theorem X1_le_U (n : ℕ) : X1 K n ≤ UpperU K n := by
  intro g hg
  obtain ⟨c, -, hc⟩ := mem_X1.mp hg
  have h : IsUpperUni (gm g) := by
    rw [hc]
    exact isUpperUni_x1Mat c
  exact mem_UpperU'.mpr h

end RootGroups

end Datum

end CFSG.HardMathSupport.U4FF
