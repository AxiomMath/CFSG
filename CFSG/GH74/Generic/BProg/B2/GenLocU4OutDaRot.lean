module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF
public import CFSG.GH74.Generic.BProg.B2.GenLocDiagU

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG.LocalAnalysis.ComponentInitial Matrix
open GenLocU4Basic GenLocU4Out

namespace GenLocU4OutDa

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def daRot (q : ℕ) (ι a b σ : K) : Matrix (Fin 4) (Fin 4) K :=
  !![(a + a ^ q) / 2, (a - a ^ q) / (2 * ι), -(σ * b + b ^ q) / 2, (b ^ q - σ * b) / (2 * ι);
     ι * (a - a ^ q) / 2, (a + a ^ q) / 2, ι * (b ^ q - σ * b) / 2, -(σ * b + b ^ q) / 2;
     (b + σ ^ q * b ^ q) / 2, (b - σ ^ q * b ^ q) / (2 * ι), (a + a ^ q) / 2, (a - a ^ q) / (2 * ι);
     ι * (b - σ ^ q * b ^ q) / 2, (b + σ ^ q * b ^ q) / 2, ι * (a - a ^ q) / 2, (a + a ^ q) / 2]

end GenLocU4OutDa

namespace GenLocU4OutDaRot

variable {K : Type} [Field K] {p f : ℕ}

open GenLocU4OutDa

@[expose] def daP (ι a a' b b' s s' : K) : Matrix (Fin 4) (Fin 4) K :=
  !![a + a', ι * (a' - a), -(s * b + b'), ι * (s * b - b');
     ι * (a - a'), a + a', ι * (b' - s * b), -(s * b + b');
     b + s' * b', ι * (s' * b' - b), a + a', ι * (a' - a);
     ι * (b - s' * b'), b + s' * b', ι * (a - a'), a + a']

theorem daRot_eq {ι : K} (hι : ι * ι = -1) (q : ℕ) (a b σ : K) :
    daRot q ι a b σ = (2 : K)⁻¹ • daP ι a (a ^ q) b (b ^ q) σ (σ ^ q) := by
  have hinv : ι⁻¹ = -ι := inv_eq_of_mul_eq_one_right (by linear_combination -hι)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [daRot, daP, div_eq_mul_inv, hinv] <;> ring

theorem daP_map (φ : K →+* K) (ι a a' b b' s s' : K) :
    (daP ι a a' b b' s s').map φ = daP (φ ι) (φ a) (φ a') (φ b) (φ b') (φ s) (φ s') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [daP]

theorem daP_conj_mul {ι a a' b b' s s' : K} (hι : ι * ι = -1) (hab : a * a + s * b * b = 1)
    (hab' : a' * a' + s' * b' * b' = 1) :
    (daP ι a' a b' b s' s)ᵀ * daP ι a a' b b' s s' = (4 : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, daP] <;>
    first
    | ring1
    | linear_combination (-a ^ 2 + 2 * a * a' - a' ^ 2 - b ^ 2 * s + b * b' * s * s' + b * b'
        - b' ^ 2 * s') * hι + 2 * hab + 2 * hab'
    | linear_combination (-2 * ι) * hab + (2 * ι) * hab'
    | linear_combination (2 * ι) * hab + (-2 * ι) * hab'

theorem det_daP {ι a a' b b' s s' : K} (hι : ι * ι = -1) (hab : a * a + s * b * b = 1)
    (hab' : a' * a' + s' * b' * b' = 1) : (daP ι a a' b b' s s').det = 16 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, daP, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  linear_combination (ι^2*a^4 - 4*ι^2*a^3*a' + 6*ι^2*a^2*a'^2 + 2*ι^2*a^2*b^2*s - 2*ι^2*a^2*b*b'*s*s'
      - 2*ι^2*a^2*b*b' + 2*ι^2*a^2*b'^2*s' - 4*ι^2*a*a'^3 - 4*ι^2*a*a'*b^2*s
      + 4*ι^2*a*a'*b*b'*s*s' + 4*ι^2*a*a'*b*b' - 4*ι^2*a*a'*b'^2*s' + ι^2*a'^4
      + 2*ι^2*a'^2*b^2*s - 2*ι^2*a'^2*b*b'*s*s' - 2*ι^2*a'^2*b*b' + 2*ι^2*a'^2*b'^2*s'
      + ι^2*b^4*s^2 - 2*ι^2*b^3*b'*s^2*s' - 2*ι^2*b^3*b'*s + ι^2*b^2*b'^2*s^2*s'^2
      + 4*ι^2*b^2*b'^2*s*s' + ι^2*b^2*b'^2 - 2*ι^2*b*b'^3*s*s'^2 - 2*ι^2*b*b'^3*s'
      + ι^2*b'^4*s'^2 + a^4 + 4*a^3*a' - 10*a^2*a'^2 + 2*a^2*b^2*s + 2*a^2*b*b'*s*s'
      + 2*a^2*b*b' - 14*a^2*b'^2*s' + 4*a*a'^3 + 4*a*a'*b^2*s + 4*a*a'*b*b'*s*s' + 4*a*a'*b*b'
      + 4*a*a'*b'^2*s' + a'^4 - 14*a'^2*b^2*s + 2*a'^2*b*b'*s*s' + 2*a'^2*b*b' + 2*a'^2*b'^2*s'
      + b^4*s^2 + 2*b^3*b'*s^2*s' + 2*b^3*b'*s + b^2*b'^2*s^2*s'^2 - 12*b^2*b'^2*s*s' + b^2*b'^2
      + 2*b*b'^3*s*s'^2 + 2*b*b'^3*s' + b'^4*s'^2) * hι + 16 * (a' * a' + s' * b' * b') * hab + 16 * hab'

theorem daP_xi (ι a a' b b' s s' : K) : daP ι a a' b b' s s' * xi = xi * daP ι a a' b b' s s' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, daP, xi] <;> ring

theorem daP_mulVec_a {ι a a' b b' s s' : K} (hι : ι * ι = -1) :
    daP ι a a' b b' s s' *ᵥ ![1, ι, 0, 0] = (2 * a) • ![1, ι, 0, 0] + (2 * b) • ![0, 0, 1, ι] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, daP] <;>
    first
    | ring1
    | linear_combination (a' - a) * hι
    | linear_combination (s' * b' - b) * hι

theorem daP_mulVec_b {ι a a' b b' s s' : K} (hι : ι * ι = -1) :
    daP ι a a' b b' s s' *ᵥ ![1, -ι, 0, 0] =
      (2 * a') • ![1, -ι, 0, 0] + (2 * (s' * b')) • ![0, 0, 1, -ι] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, daP] <;>
    first
    | ring1
    | linear_combination (a - a') * hι
    | linear_combination (b - s' * b') * hι

@[expose] def bMat (c0 d0 c1 d1 : K) : Matrix (Fin 4) (Fin 4) K :=
  !![c0, d0, 0, 0; d0, -c0, 0, 0; 0, 0, c1, d1; 0, 0, d1, -c1]

theorem daP_comm_B {ι a a' b b' s s' c0 d0 c1 d1 : K} (F1 : s' * (c0 + ι * d0) = c1 + ι * d1)
    (F2 : c0 - ι * d0 = s * (c1 - ι * d1)) (hι : ι * ι = -1) :
    bMat c0 d0 c1 d1 * daP ι a' a b' b s' s = daP ι a a' b b' s s' * bMat c0 d0 c1 d1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, daP, bMat] <;>
    first
    | ring1
    | linear_combination (-b') * F1 + (-b) * F2
    | linear_combination b' * F1 + b * F2
    | linear_combination (ι * b') * F1 + (-(ι * b)) * F2
        + (-b * d0 + b * d1 * s - b' * d0 * s' + b' * d1) * hι

theorem two_ne_zero_of_card [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) :
    (2 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  exact Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)

theorem isSquare_of_fixed [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {w : K} (hw : w ^ (p ^ f) = w) : IsSquare w := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have := Fintype.ofFinite K
  by_cases h0 : w = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨m, hm⟩ : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hring : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    rw [FiniteField.isSquare_iff hring h0, ← Nat.card_eq_fintype_card, hK, hm]
    have hw1 : w ^ (2 * m) = 1 := by
      have e : w ^ (2 * m) * w = 1 * w := by
        rw [one_mul, ← pow_succ, ← hm]; exact hw
      exact mul_right_cancel₀ h0 e
    have hdiv : ((2 * m + 1) ^ 2) / 2 = (2 * m) * (m + 1) := by
      have : (2 * m + 1) ^ 2 = 2 * ((2 * m) * (m + 1)) + 1 := by ring
      omega
    rw [hdiv, pow_mul, hw1, one_pow]

theorem bar_two_inv [Finite K] (h : UnitaryFieldData p f K) : h.bar (2 : K)⁻¹ = (2 : K)⁻¹ := by
  rw [map_inv₀, map_ofNat]

theorem daP_bar [Finite K] (h : UnitaryFieldData p f K) {ι : K} (hιq : ι ^ (p ^ f) = ι) (a b s : K) :
    (daP ι a (a ^ (p ^ f)) b (b ^ (p ^ f)) s (s ^ (p ^ f))).map (· ^ (p ^ f)) =
      daP ι (a ^ (p ^ f)) a (b ^ (p ^ f)) b (s ^ (p ^ f)) s := by
  have hfun : (fun x : K => x ^ (p ^ f)) = h.bar := funext fun x => (h.bar_apply x).symm
  rw [hfun, daP_map]
  have hι : h.bar ι = ι := hιq
  have hbb : ∀ x : K, h.bar (x ^ (p ^ f)) = x := fun x => h.bar_bar x
  rw [hι, hbb, hbb, hbb]
  rfl

theorem daRot_map [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) {ι : K} (hι : ι * ι = -1)
    (hιq : ι ^ (p ^ f) = ι) (a b σ : K) :
    (daRot (p ^ f) ι a b σ).map (· ^ (p ^ f)) =
      (2 : K)⁻¹ • daP ι (a ^ (p ^ f)) a (b ^ (p ^ f)) b (σ ^ (p ^ f)) σ := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hfun : (fun x : K => x ^ (p ^ f)) = h.bar := funext fun x => (h.bar_apply x).symm
  rw [daRot_eq hι, ← daP_bar h hιq, hfun]
  ext i j
  simp [Matrix.smul_apply, bar_two_inv h]

theorem bar_add_mul [Finite K] (h : UnitaryFieldData p f K) {ι : K} (hιq : ι ^ (p ^ f) = ι) (x y : K) :
    (x + ι * y) ^ (p ^ f) = x ^ (p ^ f) + ι * y ^ (p ^ f) := by
  have e : h.bar (x + ι * y) = h.bar x + h.bar ι * h.bar y := by rw [map_add, map_mul]
  have e2 : h.bar ι = ι := hιq
  rw [e2] at e
  exact e

theorem bMat_unitary {q : ℕ} [Finite K] {c0 d0 c1 d1 : K} (hU : IsUnitaryU q (bMat c0 d0 c1 d1)) :
    c0 ^ q * c0 + d0 ^ q * d0 = 1 ∧ c0 ^ q * d0 - d0 ^ q * c0 = 0 ∧
      c1 ^ q * c1 + d1 ^ q * d1 = 1 ∧ c1 ^ q * d1 - d1 ^ q * c1 = 0 := by
  have hU00 := congrFun (congrFun hU 0) 0
  have hU01 := congrFun (congrFun hU 0) 1
  have hU22 := congrFun (congrFun hU 2) 2
  have hU23 := congrFun (congrFun hU 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, bMat] at hU00 hU01 hU22 hU23
  exact ⟨by linear_combination hU00, by linear_combination hU01, by linear_combination hU22,
    by linear_combination hU23⟩

theorem B_shape (h2 : (2 : K) ≠ 0) {B : Matrix (Fin 4) (Fin 4) K} (htB : tT * B = B * tT)
    (hxiB : xi * B = -(B * xi)) : B = bMat (B 0 0) (B 0 1) (B 2 2) (B 2 3) := by
  have key : ∀ i j : Fin 4, (![1, 1, -1, -1] : Fin 4 → K) i * B i j =
      B i j * (![1, 1, -1, -1] : Fin 4 → K) j := by
    intro i j
    have := congrFun (congrFun htB i) j
    simpa [tT, Matrix.diagonal_mul, Matrix.mul_diagonal] using this
  have half : ∀ x : K, x * (-1) = 1 * x → x = 0 := fun x hx => by
    have : (2 : K) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have half' : ∀ x : K, x * 1 = (-1) * x → x = 0 := fun x hx => by
    have : (2 : K) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have z02 : B 0 2 = 0 := half _ (by simpa using (key 0 2).symm)
  have z03 : B 0 3 = 0 := half _ (by simpa using (key 0 3).symm)
  have z12 : B 1 2 = 0 := half _ (by simpa using (key 1 2).symm)
  have z13 : B 1 3 = 0 := half _ (by simpa using (key 1 3).symm)
  have z20 : B 2 0 = 0 := half' _ (by simpa using (key 2 0).symm)
  have z21 : B 2 1 = 0 := half' _ (by simpa using (key 2 1).symm)
  have z30 : B 3 0 = 0 := half' _ (by simpa using (key 3 0).symm)
  have z31 : B 3 1 = 0 := half' _ (by simpa using (key 3 1).symm)
  have e00 := congrFun (congrFun hxiB 0) 0
  have e01 := congrFun (congrFun hxiB 0) 1
  have e22 := congrFun (congrFun hxiB 2) 2
  have e23 := congrFun (congrFun hxiB 2) 3
  simp [xi, Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e22 e23
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, z02, z03, z12, z13, z20, z21, z30, z31]
  · linear_combination e00
  · linear_combination e01
  · linear_combination e22
  · linear_combination e23

theorem not_fixed_of_nonsquare [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {σ a b : K} (hσ : ∀ t : K, t * t ≠ σ) (hab : a * a + σ * b * b = 1) (hb : b ≠ 0) :
    (a * a) ^ (p ^ f) ≠ a * a := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  intro hcon
  have hw : (σ * b * b) ^ (p ^ f) = σ * b * b := by
    have e : σ * b * b = 1 - a * a := by linear_combination hab
    have e2 : h.bar (1 - a * a) = 1 - h.bar (a * a) := by rw [map_sub, map_one]
    have e3 : h.bar (a * a) = a * a := hcon
    rw [e3] at e2
    rw [e]
    exact e2
  obtain ⟨u, hu⟩ := isSquare_of_fixed hp hp2 hK hw
  refine hσ (u / b) ?_
  field_simp
  linear_combination -hu

end GenLocU4OutDaRot

namespace GenLocU4OutDa

open GenLocU4OutDaRot

variable {K : Type} [Field K] {p f : ℕ} [Finite K]

theorem daRot_mem (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {ι a b σ : K} (hι : ι * ι = -1)
    (hιq : ι ^ (p ^ f) = ι) (hab : a * a + σ * b * b = 1) :
    IsUnitaryU (p ^ f) (daRot (p ^ f) ι a b σ) ∧ (daRot (p ^ f) ι a b σ).det = 1 ∧
      daRot (p ^ f) ι a b σ * xi = xi * daRot (p ^ f) ι a b σ ∧
      daRot (p ^ f) ι a b σ *ᵥ ![1, ι, 0, 0] = a • ![1, ι, 0, 0] + b • ![0, 0, 1, ι] ∧
      daRot (p ^ f) ι a b σ *ᵥ ![1, -ι, 0, 0] = a ^ (p ^ f) • ![1, -ι, 0, 0] + (σ ^ (p ^ f) * b ^ (p ^ f)) • ![0, 0, 1, -ι] := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hab' : a ^ (p ^ f) * a ^ (p ^ f) + σ ^ (p ^ f) * b ^ (p ^ f) * b ^ (p ^ f) = 1 := by
    have := congrArg h.bar hab
    simp only [map_add, map_mul, map_one] at this
    exact this
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have h22' : ∀ x : K, (2 : K)⁻¹ * (2 * x) = x := fun x => by rw [← mul_assoc, h22, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold IsUnitaryU
    rw [daRot_map hp hK hι hιq, daRot_eq hι]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      daP_conj_mul hι hab hab']
    have h4 : ((2 : K)⁻¹ * ((2 : K)⁻¹ * 4)) = 1 := by
      linear_combination ((2 : K)⁻¹ * 2 + 1) * h22
    rw [h4, one_smul]
  · rw [daRot_eq hι, Matrix.det_smul, det_daP hι hab hab']
    simp only [Fintype.card_fin]
    linear_combination (((2 : K)⁻¹ * 2) ^ 3 + ((2 : K)⁻¹ * 2) ^ 2 + (2 : K)⁻¹ * 2 + 1) * h22
  · rw [daRot_eq hι, Matrix.smul_mul, Matrix.mul_smul, daP_xi]
  · rw [daRot_eq hι, Matrix.smul_mulVec, daP_mulVec_a hι, smul_add, smul_smul, smul_smul, h22', h22']
  · rw [daRot_eq hι, Matrix.smul_mulVec, daP_mulVec_b hι, smul_add, smul_smul, smul_smul, h22', h22']

theorem daRot_fixOut (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {ι a b σ : K} (hι : ι * ι = -1)
    (hιq : ι ^ (p ^ f) = ι) (hab : a * a + σ * b * b = 1) (B : Matrix (Fin 4) (Fin 4) K)
    (hBU : IsUnitaryU (p ^ f) B) (hBs : Bᵀ = B) (htB : tT * B = B * tT) (hxiB : xi * B = -(B * xi))
    (hσ : σ * (B 0 0 + ι * B 0 1) ^ (p ^ f) = (B 2 2 + ι * B 2 3) ^ (p ^ f)) :
    B * (daRot (p ^ f) ι a b σ).map (· ^ (p ^ f)) = daRot (p ^ f) ι a b σ * B := by
  have _ := hab
  have _ := hBs
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  obtain ⟨c0, d0, c1, d1, hB⟩ : ∃ c0 d0 c1 d1 : K, B = bMat c0 d0 c1 d1 :=
    ⟨_, _, _, _, B_shape h2 htB hxiB⟩
  subst hB
  obtain ⟨hU00, hU01, hU22, hU23⟩ := bMat_unitary hBU
  have hσ1 : σ * (c0 + ι * d0) ^ (p ^ f) = (c1 + ι * d1) ^ (p ^ f) := by simpa [bMat] using hσ
  have hbar := bar_add_mul h hιq
  have bb : ∀ x : K, (x ^ (p ^ f)) ^ (p ^ f) = x := fun x => h.bar_bar x
  have hσ2 : σ * (c0 ^ (p ^ f) + ι * d0 ^ (p ^ f)) = c1 ^ (p ^ f) + ι * d1 ^ (p ^ f) := by
    rw [← hbar, ← hbar]; exact hσ1
  have e0 : (c0 ^ (p ^ f) + ι * d0 ^ (p ^ f)) * (c0 - ι * d0) = 1 := by
    linear_combination hU00 - ι * hU01 - (d0 ^ (p ^ f) * d0) * hι
  have e1 : (c1 ^ (p ^ f) + ι * d1 ^ (p ^ f)) * (c1 - ι * d1) = 1 := by
    linear_combination hU22 - ι * hU23 - (d1 ^ (p ^ f) * d1) * hι
  have F2 : c0 - ι * d0 = σ * (c1 - ι * d1) := by
    linear_combination (σ * (c1 - ι * d1)) * e0 + (-(c0 - ι * d0)) * e1
      - ((c0 - ι * d0) * (c1 - ι * d1)) * hσ2
  have F1 : σ ^ (p ^ f) * (c0 + ι * d0) = c1 + ι * d1 := by
    have := congrArg (fun x : K => x ^ (p ^ f)) hσ1
    simp only [mul_pow] at this
    rwa [bb, bb] at this
  rw [daRot_map hp hK hι hιq, daRot_eq hι, Matrix.mul_smul, Matrix.smul_mul,
    daP_comm_B F1 F2 hι]

theorem exists_rot_param (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {σ : K} (hσ : ∀ t : K, t * t ≠ σ) :
    ∃ a b : K, a * a + σ * b * b = 1 ∧ b ≠ 0 ∧ (a * a) ^ (p ^ f) ≠ a * a := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
  have hm1 : (-1 : K) ^ (p ^ f) = -1 := hodd.neg_one_pow
  obtain ⟨r, hr⟩ := isSquare_of_fixed hp hp2 hK hm1
  have hσ1 : 1 + σ ≠ 0 := fun h1 => hσ r (by linear_combination -hr - h1)
  have hab : ((1 - σ) / (1 + σ)) * ((1 - σ) / (1 + σ)) + σ * (2 / (1 + σ)) * (2 / (1 + σ)) = 1 := by
    field_simp
    ring
  have hb0 : (2 / (1 + σ) : K) ≠ 0 := div_ne_zero h2 hσ1
  exact ⟨_, _, hab, hb0, not_fixed_of_nonsquare hp hK hp2 hσ hab hb0⟩

end GenLocU4OutDa

end CFSG.GH74.Generic.BProg.B2
