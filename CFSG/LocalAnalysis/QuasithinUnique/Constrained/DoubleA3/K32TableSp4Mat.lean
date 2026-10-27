module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableReg
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Polynomial Matrix

section Setup

variable {K : Type*} [Field K]

@[expose] def k32J (K : Type*) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i.val + j.val = 3 then 1 else 0

@[expose] def k32UMat (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, a, b, c; 0, 1, d, b + a * d; 0, 0, 1, a; 0, 0, 0, 1]

@[expose] def K32Dep3 (b₁ c₁ d₁ b₂ c₂ d₂ : K) : Prop :=
  b₁ * c₂ = b₂ * c₁ ∧ b₁ * d₂ = b₂ * d₁ ∧ c₁ * d₂ = c₂ * d₁

theorem k32UMat_sub_one_pow_four (a b c d : K) : (k32UMat a b c d - 1) ^ 4 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, k32UMat, Matrix.one_apply]

theorem k32UMat_cyclic [CharP K 2] {a b c d : K} (ha : a ≠ 0) (hd : d ≠ 0) (w : Fin 4 → K) :
    ∃ p : K[X], w = (aeval (k32UMat a b c d - 1) p).mulVec (Pi.single 3 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set N : Matrix (Fin 4) (Fin 4) K := k32UMat a b c d - 1 with hN
  have v1 : N.mulVec (Pi.single 3 1) = ![c, b + a * d, a, 0] := by
    ext i
    fin_cases i <;>
      simp [hN, k32UMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
  have v2 : N.mulVec ![c, b + a * d, a, 0] = ![a ^ 2 * d, a * d, 0, 0] := by
    ext i
    fin_cases i <;>
      simp [hN, k32UMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    all_goals first | ring1 | linear_combination (a * b) * h2
  have v3 : N.mulVec ![a ^ 2 * d, a * d, 0, 0] = ![a ^ 2 * d, 0, 0, 0] := by
    ext i
    fin_cases i <;>
      simp [hN, k32UMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
    all_goals ring1
  have had : a * d ≠ 0 := mul_ne_zero ha hd
  have ha2d : a ^ 2 * d ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha) hd
  set x₀ := w 3 with hx₀
  set x₁ := w 2 / a with hx₁
  set x₂ := (w 1 - x₁ * (b + a * d)) / (a * d) with hx₂
  set x₃ := (w 0 - x₁ * c - x₂ * (a ^ 2 * d)) / (a ^ 2 * d) with hx₃
  refine ⟨C x₀ + C x₁ * X + C x₂ * X ^ 2 + C x₃ * X ^ 3, ?_⟩
  have e0 : (aeval N) (C x₀ + C x₁ * X + C x₂ * X ^ 2 + C x₃ * X ^ 3) =
      x₀ • (1 : Matrix (Fin 4) (Fin 4) K) + x₁ • N + x₂ • N ^ 2 + x₃ • N ^ 3 := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e0]
  have hN2 : N ^ 2 = N * N := pow_two N
  have hN3 : N ^ 3 = N * (N * N) := by rw [pow_succ', pow_two]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hN2, hN3,
    ← Matrix.mulVec_mulVec, v1, v2, v3]
  ext i
  fin_cases i
  · simp [Matrix.vecHead, Matrix.vecTail]
    rw [hx₃]
    field_simp
    ring
  · simp [Matrix.vecHead, Matrix.vecTail]
    rw [hx₂]
    field_simp
    ring
  · simp [Matrix.vecHead, Matrix.vecTail]
    rw [hx₁]
    field_simp
  · simp [Matrix.vecHead, Matrix.vecTail]
    exact hx₀.symm

theorem k32UMat_commute_scalar [CharP K 2] {a b c d : K} (ha : a ≠ 0) (hd : d ≠ 0)
    {M : Matrix (Fin 4) (Fin 4) K} (hcomm : M * k32UMat a b c d = k32UMat a b c d * M) {c' : K}
    (hc : c' ≠ 0) (hM : M ^ 3 = c' • (1 : Matrix (Fin 4) (Fin 4) K)) :
    ∃ x : K, M = x • (1 : Matrix (Fin 4) (Fin 4) K) := by
  set φ := Matrix.toLinAlgEquiv' (R := K) (n := Fin 4) with hφ
  have hu : Commute (k32UMat a b c d) M := hcomm.symm
  have hNM : Commute (k32UMat a b c d - 1) M := hu.sub_left (Commute.one_left M)
  have hNM' : Commute (φ (k32UMat a b c d - 1)) (φ M) := hNM.map φ
  have hnil : IsNilpotent (φ (k32UMat a b c d - 1)) :=
    IsNilpotent.map ⟨4, k32UMat_sub_one_pow_four a b c d⟩ φ
  have hcyc : ∀ w : Fin 4 → K, ∃ p : K[X],
      w = (aeval (φ (k32UMat a b c d - 1)) p) (Pi.single 3 1 : Fin 4 → K) := by
    intro w
    obtain ⟨p, hp⟩ := k32UMat_cyclic (b := b) (c := c) ha hd w
    refine ⟨p, ?_⟩
    rw [aeval_algHom_apply]
    simpa [hφ, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply] using hp
  have hA : φ M ^ 3 = algebraMap K (Module.End K (Fin 4 → K)) c' := by
    rw [← map_pow, hM, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
  obtain ⟨x, hx⟩ := k32_scalar_of_commute_cyclic hNM' hnil hcyc hc hA
  refine ⟨x, φ.injective ?_⟩
  rw [hx, map_smul, map_one, Algebra.algebraMap_eq_smul_one]

theorem k32_reg_eq_one [CharP K 2] {a b c d : K} (ha : a ≠ 0) (hd : d ≠ 0)
    {M : Matrix (Fin 4) (Fin 4) K} (hsp : Mᵀ * k32J K * M = k32J K) (hM3 : M ^ 3 = 1)
    (hcomm : M * k32UMat a b c d = k32UMat a b c d * M) : M = 1 := by
  obtain ⟨x, hx⟩ := k32UMat_commute_scalar ha hd hcomm one_ne_zero
    (by rw [hM3, one_smul])
  have h03 := congrFun (congrFun hsp 0) 3
  rw [hx] at h03
  simp [Matrix.mul_apply, k32J, Matrix.smul_apply, Matrix.one_apply] at h03
  have hx1 : x = 1 := by
    have h2 : (x + 1) ^ 2 = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h03 + (x + 1) * h2'
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact CharTwo.add_eq_zero.mp this
  rw [hx, hx1, one_smul]

theorem k32_comm_entries {M : Matrix (Fin 4) (Fin 4) K} {b c d : K}
    (h : M * k32UMat 0 b c d = k32UMat 0 b c d * M) :
    b * M 2 0 + c * M 3 0 = 0 ∧ b * M 2 1 + c * M 3 1 = 0 ∧
    d * M 2 0 + b * M 3 0 = 0 ∧ d * M 2 1 + b * M 3 1 = 0 ∧
    M 2 0 * b + M 2 1 * d = 0 ∧ M 2 0 * c + M 2 1 * b = 0 ∧
    M 3 0 * b + M 3 1 * d = 0 ∧ M 3 0 * c + M 3 1 * b = 0 ∧
    M 0 0 * b + M 0 1 * d = b * M 2 2 + c * M 3 2 ∧
    M 0 0 * c + M 0 1 * b = b * M 2 3 + c * M 3 3 ∧
    M 1 0 * b + M 1 1 * d = d * M 2 2 + b * M 3 2 ∧
    M 1 0 * c + M 1 1 * b = d * M 2 3 + b * M 3 3 := by
  have e : ∀ i j : Fin 4, (M * k32UMat 0 b c d) i j = (k32UMat 0 b c d * M) i j := fun i j => by
    rw [h]
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  have h22 := e 2 2
  have h23 := e 2 3
  have h32 := e 3 2
  have h33 := e 3 3
  have h02 := e 0 2
  have h03 := e 0 3
  have h12 := e 1 2
  have h13 := e 1 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, k32UMat] at h00 h01 h10 h11 h22 h23 h32 h33
  simp [Matrix.mul_apply, Fin.sum_univ_four, k32UMat] at h02 h03 h12 h13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -h00
  · linear_combination -h01
  · linear_combination -h10
  · linear_combination -h11
  · linear_combination h22
  · linear_combination h23
  · linear_combination h32
  · linear_combination h33
  · linear_combination h02
  · linear_combination h03
  · linear_combination h12
  · linear_combination h13

theorem k32_A1a_p {p q : K} (hp : p ≠ 0) {b₁ c₁ d₁ b₂ c₂ d₂ : K}
    (e5₁ : p * b₁ + q * d₁ = 0) (e6₁ : p * c₁ + q * b₁ = 0)
    (e5₂ : p * b₂ + q * d₂ = 0) (e6₂ : p * c₂ + q * b₂ = 0) :
    K32Dep3 b₁ c₁ d₁ b₂ c₂ d₂ := by
  have hb₁ : p ^ 2 * c₁ = q ^ 2 * d₁ := by linear_combination p * e6₁ - q * e5₁
  have hb₂ : p ^ 2 * c₂ = q ^ 2 * d₂ := by linear_combination p * e6₂ - q * e5₂
  refine ⟨?_, ?_, ?_⟩
  · have : p ^ 3 * (b₁ * c₂ - b₂ * c₁) = 0 := by
      linear_combination (p ^ 2 * c₂) * e5₁ - (p ^ 2 * c₁) * e5₂ - (q * d₁) * hb₂ + (q * d₂) * hb₁
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hp)
    linear_combination this
  · have : p * (b₁ * d₂ - b₂ * d₁) = 0 := by linear_combination d₂ * e5₁ - d₁ * e5₂
    have := (mul_eq_zero.mp this).resolve_left hp
    linear_combination this
  · have : p ^ 2 * (c₁ * d₂ - c₂ * d₁) = 0 := by linear_combination d₂ * hb₁ - d₁ * hb₂
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hp)
    linear_combination this

theorem k32_A1a {p q r s : K} (hγ : ¬ (p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0))
    {b₁ c₁ d₁ b₂ c₂ d₂ : K}
    (e1₁ : b₁ * p + c₁ * r = 0) (e2₁ : b₁ * q + c₁ * s = 0) (e3₁ : d₁ * p + b₁ * r = 0)
    (e4₁ : d₁ * q + b₁ * s = 0) (e5₁ : p * b₁ + q * d₁ = 0) (e6₁ : p * c₁ + q * b₁ = 0)
    (e7₁ : r * b₁ + s * d₁ = 0) (e8₁ : r * c₁ + s * b₁ = 0)
    (e1₂ : b₂ * p + c₂ * r = 0) (e2₂ : b₂ * q + c₂ * s = 0) (e3₂ : d₂ * p + b₂ * r = 0)
    (e4₂ : d₂ * q + b₂ * s = 0) (e5₂ : p * b₂ + q * d₂ = 0) (e6₂ : p * c₂ + q * b₂ = 0)
    (e7₂ : r * b₂ + s * d₂ = 0) (e8₂ : r * c₂ + s * b₂ = 0) :
    K32Dep3 b₁ c₁ d₁ b₂ c₂ d₂ := by
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · by_cases hr : r = 0
      · have hs : s ≠ 0 := fun hs => hγ ⟨hp, hq, hr, hs⟩
        have hc₁ : c₁ = 0 := by
          have : c₁ * s = 0 := by linear_combination e2₁ - b₁ * hq
          exact (mul_eq_zero.mp this).resolve_right hs
        have hb₁ : b₁ = 0 := by
          have : b₁ * s = 0 := by linear_combination e4₁ - d₁ * hq
          exact (mul_eq_zero.mp this).resolve_right hs
        have hc₂ : c₂ = 0 := by
          have : c₂ * s = 0 := by linear_combination e2₂ - b₂ * hq
          exact (mul_eq_zero.mp this).resolve_right hs
        have hb₂ : b₂ = 0 := by
          have : b₂ * s = 0 := by linear_combination e4₂ - d₂ * hq
          exact (mul_eq_zero.mp this).resolve_right hs
        subst hc₁ hb₁ hc₂ hb₂
        exact ⟨by ring, by ring, by ring⟩
      · have hc₁ : c₁ = 0 := by
          have : c₁ * r = 0 := by linear_combination e1₁ - b₁ * hp
          exact (mul_eq_zero.mp this).resolve_right hr
        have hb₁ : b₁ = 0 := by
          have : b₁ * r = 0 := by linear_combination e3₁ - d₁ * hp
          exact (mul_eq_zero.mp this).resolve_right hr
        have hc₂ : c₂ = 0 := by
          have : c₂ * r = 0 := by linear_combination e1₂ - b₂ * hp
          exact (mul_eq_zero.mp this).resolve_right hr
        have hb₂ : b₂ = 0 := by
          have : b₂ * r = 0 := by linear_combination e3₂ - d₂ * hp
          exact (mul_eq_zero.mp this).resolve_right hr
        subst hc₁ hb₁ hc₂ hb₂
        exact ⟨by ring, by ring, by ring⟩
    · have hd₁ : d₁ = 0 := by
        have : q * d₁ = 0 := by linear_combination e5₁ - b₁ * hp
        exact (mul_eq_zero.mp this).resolve_left hq
      have hb₁ : b₁ = 0 := by
        have : q * b₁ = 0 := by linear_combination e6₁ - c₁ * hp
        exact (mul_eq_zero.mp this).resolve_left hq
      have hd₂ : d₂ = 0 := by
        have : q * d₂ = 0 := by linear_combination e5₂ - b₂ * hp
        exact (mul_eq_zero.mp this).resolve_left hq
      have hb₂ : b₂ = 0 := by
        have : q * b₂ = 0 := by linear_combination e6₂ - c₂ * hp
        exact (mul_eq_zero.mp this).resolve_left hq
      subst hd₁ hb₁ hd₂ hb₂
      exact ⟨by ring, by ring, by ring⟩
  · exact k32_A1a_p hp e5₁ e6₁ e5₂ e6₂

theorem k32_A1b [CharP K 2] {b₁ c₁ d₁ b₂ c₂ d₂ : K} (hQ₁ : b₁ ^ 2 + c₁ * d₁ = 0)
    (hQ₂ : b₂ ^ 2 + c₂ * d₂ = 0) (hB : c₁ * d₂ + c₂ * d₁ = 0) : K32Dep3 b₁ c₁ d₁ b₂ c₂ d₂ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_, ?_⟩
  · have h : (b₁ * c₂ + b₂ * c₁) ^ 2 = 0 := by
      linear_combination (c₂ ^ 2) * hQ₁ + (c₁ ^ 2) * hQ₂ - (c₁ * c₂) * hB +
        (b₁ * b₂ * c₁ * c₂) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h
    linear_combination this - (b₂ * c₁) * h2
  · have h : (b₁ * d₂ + b₂ * d₁) ^ 2 = 0 := by
      linear_combination (d₂ ^ 2) * hQ₁ + (d₁ ^ 2) * hQ₂ - (d₁ * d₂) * hB +
        (b₁ * b₂ * d₁ * d₂) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h
    linear_combination this - (b₂ * d₁) * h2
  · linear_combination hB - (c₂ * d₁) * h2

theorem k32_A1c [CharP K 2] {M : Matrix (Fin 4) (Fin 4) K}
    (hsp : Mᵀ * k32J K * M = k32J K) (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1)
    (hp : M 2 0 = 0) (hq : M 2 1 = 0) (hr : M 3 0 = 0) (hs : M 3 1 = 0)
    {b₀ c₀ d₀ : K} (hQ : b₀ ^ 2 + c₀ * d₀ ≠ 0)
    (h₀ : M * k32UMat 0 b₀ c₀ d₀ = k32UMat 0 b₀ c₀ d₀ * M)
    {b c d : K} (h : M * k32UMat 0 b c d = k32UMat 0 b c d * M) : c = 0 ∧ d = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, -, -, -, -, -, -, -, f1, f2, f3, f4⟩ := k32_comm_entries h
  obtain ⟨-, -, -, -, -, -, -, -, g1, g2, g3, g4⟩ := k32_comm_entries h₀
  have eS : ∀ i j : Fin 4, (Mᵀ * k32J K * M) i j = k32J K i j := fun i j => by rw [hsp]
  have s1 := eS 0 2
  have s2 := eS 0 3
  have s3 := eS 1 2
  have s4 := eS 1 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, k32J, hp, hq, hr, hs] at s1 s2 s3 s4
  have c00 := congrFun (congrFun hM3 0) 0
  have c01 := congrFun (congrFun hM3 0) 1
  have c10 := congrFun (congrFun hM3 1) 0
  have c11 := congrFun (congrFun hM3 1) 1
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, hp, hq, hr, hs] at c00 c01 c10 c11
  have hQ' : b₀ ^ 2 - c₀ * d₀ ≠ 0 := by
    intro h0
    apply hQ
    linear_combination h0 + (c₀ * d₀) * h2
  set a := M 0 0 with ha
  set b' := M 0 1 with hb'
  set c' := M 1 0 with hc'
  set d' := M 1 1 with hd'
  set e := M 2 2 with he
  set f := M 2 3 with hf
  set g := M 3 2 with hg
  set k := M 3 3 with hk
  have D1 : (a * d' - b' * c') * (e * k - f * g) = 1 := by
    linear_combination (d' * e + b' * g) * s2 + s3 - (d' * f + b' * k) * s1
  have D2 : (b₀ ^ 2 - c₀ * d₀) * ((a * d' - b' * c') - (e * k - f * g)) = 0 := by
    linear_combination (c' * c₀ + d' * b₀) * g1 + (b₀ * e + c₀ * g) * g4 -
      (c' * b₀ + d' * d₀) * g2 - (b₀ * f + c₀ * k) * g3
  have hεδ : a * d' - b' * c' = e * k - f * g :=
    sub_eq_zero.mp ((mul_eq_zero.mp D2).resolve_left hQ')
  have hε2 : (a * d' - b' * c') * (a * d' - b' * c') = 1 := by
    rw [← hεδ] at D1
    exact D1
  have hε1 : a * d' - b' * c' = 1 := by
    have : (a * d' - b' * c' - 1) ^ 2 = 0 := by
      linear_combination hε2 + (1 - (a * d' - b' * c')) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linear_combination this
  have he' : e = a := by linear_combination a * s3 - b' * s1 - e * hε1
  have hf' : f = b' := by linear_combination a * s4 - b' * s2 - f * hε1 - b' * h2
  have hg' : g = c' := by linear_combination d' * s1 - c' * s3 - g * hε1 - c' * h2
  have hk' : k = d' := by linear_combination d' * s2 - c' * s4 - k * hε1
  have hc : c * (a - d') = 0 := by linear_combination f2 + b * hf' + c * hk'
  have hd : d * (a - d') = 0 := by linear_combination -f3 - d * he' - b * hg'
  have htr : a - d' ≠ 0 := by
    intro hh
    have hh' : d' = a := by linear_combination -hh
    have hP : a ^ 2 + b' * c' = 1 := by linear_combination hε1 + a * hh + (b' * c') * h2
    have ha1 : a = 1 := by
      linear_combination c00 - a * hP - (a * b' * c') * h2 - (b' * c') * hh'
    have hd1 : d' = 1 := by linear_combination hh' + ha1
    have hbc : b' * c' = 0 := by
      have h1 := hP
      rw [ha1] at h1
      linear_combination h1
    have hb0 : b' = 0 := by
      rw [ha1, hd1] at c01
      linear_combination c01 - b' * hbc - b' * h2
    have hc0 : c' = 0 := by
      rw [ha1, hd1] at c10
      linear_combination c10 - c' * hbc - c' * h2
    apply hM1
    have hM00 : M 0 0 = 1 := ha1
    have hM01 : M 0 1 = 0 := hb0
    have hM10 : M 1 0 = 0 := hc0
    have hM11 : M 1 1 = 1 := hd1
    have hM22 : M 2 2 = 1 := he'.trans ha1
    have hM23 : M 2 3 = 0 := hf'.trans hb0
    have hM32 : M 3 2 = 0 := hg'.trans hc0
    have hM33 : M 3 3 = 1 := hk'.trans hd1
    have c02 := congrFun (congrFun hM3 0) 2
    have c03 := congrFun (congrFun hM3 0) 3
    have c12 := congrFun (congrFun hM3 1) 2
    have c13 := congrFun (congrFun hM3 1) 3
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, hp, hq, hr, hs, hM00, hM01, hM10, hM11,
      hM22, hM23, hM32, hM33] at c02 c03 c12 c13
    have m02 : M 0 2 = 0 := by linear_combination c02 - M 0 2 * h2
    have m03 : M 0 3 = 0 := by linear_combination c03 - M 0 3 * h2
    have m12 : M 1 2 = 0 := by linear_combination c12 - M 1 2 * h2
    have m13 : M 1 3 = 0 := by linear_combination c13 - M 1 3 * h2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM00, hM01, hM10, hM11, hM22, hM23, hM32, hM33, hp, hq, hr, hs, m02, m03, m12, m13]
  exact ⟨(mul_eq_zero.mp hc).resolve_right htr, (mul_eq_zero.mp hd).resolve_right htr⟩

theorem k32UMat_zero_add (b₁ c₁ d₁ b₂ c₂ d₂ : K) :
    k32UMat 0 (b₁ + b₂) (c₁ + c₂) (d₁ + d₂) =
      k32UMat 0 b₁ c₁ d₁ + k32UMat 0 b₂ c₂ d₂ - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k32UMat]

theorem k32_sigma_dep [CharP K 2] {M : Matrix (Fin 4) (Fin 4) K}
    (hsp : Mᵀ * k32J K * M = k32J K) (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1)
    {b₁ c₁ d₁ b₂ c₂ d₂ : K}
    (h₁ : M * k32UMat 0 b₁ c₁ d₁ = k32UMat 0 b₁ c₁ d₁ * M)
    (h₂ : M * k32UMat 0 b₂ c₂ d₂ = k32UMat 0 b₂ c₂ d₂ * M) : K32Dep3 b₁ c₁ d₁ b₂ c₂ d₂ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hγ : M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 3 0 = 0 ∧ M 3 1 = 0
  · obtain ⟨hp, hq, hr, hs⟩ := hγ
    have h₃ : M * k32UMat 0 (b₁ + b₂) (c₁ + c₂) (d₁ + d₂) =
        k32UMat 0 (b₁ + b₂) (c₁ + c₂) (d₁ + d₂) * M := by
      rw [k32UMat_zero_add, mul_sub, sub_mul, mul_add, add_mul, h₁, h₂, mul_one, one_mul]
    have key : ∀ {b₀ c₀ d₀ : K}, b₀ ^ 2 + c₀ * d₀ ≠ 0 →
        M * k32UMat 0 b₀ c₀ d₀ = k32UMat 0 b₀ c₀ d₀ * M → K32Dep3 b₁ c₁ d₁ b₂ c₂ d₂ := by
      intro b₀ c₀ d₀ hQ h₀
      obtain ⟨hc₁, hd₁⟩ := k32_A1c hsp hM3 hM1 hp hq hr hs hQ h₀ h₁
      obtain ⟨hc₂, hd₂⟩ := k32_A1c hsp hM3 hM1 hp hq hr hs hQ h₀ h₂
      subst hc₁ hd₁ hc₂ hd₂
      exact ⟨by ring, by ring, by ring⟩
    by_cases hQ₁ : b₁ ^ 2 + c₁ * d₁ = 0
    · by_cases hQ₂ : b₂ ^ 2 + c₂ * d₂ = 0
      · by_cases hQ₃ : (b₁ + b₂) ^ 2 + (c₁ + c₂) * (d₁ + d₂) = 0
        · have hB : c₁ * d₂ + c₂ * d₁ = 0 := by
            linear_combination hQ₃ - hQ₁ - hQ₂ - (b₁ * b₂) * h2
          exact k32_A1b hQ₁ hQ₂ hB
        · exact key hQ₃ h₃
      · exact key hQ₂ h₂
    · exact key hQ₁ h₁
  · obtain ⟨e1₁, e2₁, e3₁, e4₁, e5₁, e6₁, e7₁, e8₁, -⟩ := k32_comm_entries h₁
    obtain ⟨e1₂, e2₂, e3₂, e4₂, e5₂, e6₂, e7₂, e8₂, -⟩ := k32_comm_entries h₂
    exact k32_A1a hγ e1₁ e2₁ e3₁ e4₁ e5₁ e6₁ e7₁ e8₁ e1₂ e2₂ e3₂ e4₂ e5₂ e6₂ e7₂ e8₂


theorem k32_dep3_eq_of_b {b₀ c₀ d₀ b c d b' c' d' : K} (hb₀ : b₀ ≠ 0)
    (h : K32Dep3 b c d b₀ c₀ d₀) (h' : K32Dep3 b' c' d' b₀ c₀ d₀) (hbb : b = b') :
    c = c' ∧ d = d' := by
  subst hbb
  exact ⟨mul_left_cancel₀ hb₀ (h.1.symm.trans h'.1), mul_left_cancel₀ hb₀ (h.2.1.symm.trans h'.2.1)⟩

theorem k32_dep3_eq_of_c {b₀ c₀ d₀ b c d b' c' d' : K} (hc₀ : c₀ ≠ 0)
    (h : K32Dep3 b c d b₀ c₀ d₀) (h' : K32Dep3 b' c' d' b₀ c₀ d₀) (hcc : c = c') :
    b = b' ∧ d = d' := by
  subst hcc
  refine ⟨mul_right_cancel₀ hc₀ (h.1.trans h'.1.symm), mul_left_cancel₀ hc₀ ?_⟩
  have e1 := h.2.2
  have e2 := h'.2.2
  linear_combination -e1 + e2

theorem k32_dep3_eq_of_d {b₀ c₀ d₀ b c d b' c' d' : K} (hd₀ : d₀ ≠ 0)
    (h : K32Dep3 b c d b₀ c₀ d₀) (h' : K32Dep3 b' c' d' b₀ c₀ d₀) (hdd : d = d') :
    b = b' ∧ c = c' := by
  subst hdd
  refine ⟨mul_right_cancel₀ hd₀ (h.2.1.trans h'.2.1.symm), mul_right_cancel₀ hd₀ ?_⟩
  exact h.2.2.trans h'.2.2.symm

theorem k32_card_le_of_dep3 {T : Type*} [Finite T] {F : Type*} [Field F] [Finite F]
    (σ : T → F × F × F) (hσ : Function.Injective σ)
    (hdep : ∀ s t, K32Dep3 (σ s).1 (σ s).2.1 (σ s).2.2 (σ t).1 (σ t).2.1 (σ t).2.2) :
    Nat.card T ≤ Nat.card F := by
  by_cases hz : ∀ s, σ s = 0
  · have hsub : Subsingleton T := ⟨fun s t => hσ ((hz s).trans (hz t).symm)⟩
    have h1 : Nat.card T ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    exact h1.trans (Nat.succ_le_of_lt Nat.card_pos)
  · push Not at hz
    obtain ⟨s₀, hs₀⟩ := hz
    rcases hσs : σ s₀ with ⟨b₀, c₀, d₀⟩
    rw [hσs] at hs₀
    have hdep' : ∀ t, K32Dep3 (σ t).1 (σ t).2.1 (σ t).2.2 b₀ c₀ d₀ := fun t => by
      have := hdep t s₀
      rwa [hσs] at this
    by_cases hb₀ : b₀ = 0
    · by_cases hc₀ : c₀ = 0
      · have hd₀ : d₀ ≠ 0 := fun hd₀ => hs₀ (by rw [hb₀, hc₀, hd₀]; rfl)
        refine Nat.card_le_card_of_injective (fun t => (σ t).2.2) fun t t' htt => hσ ?_
        obtain ⟨h1, h2⟩ := k32_dep3_eq_of_d hd₀ (hdep' t) (hdep' t') htt
        exact Prod.ext h1 (Prod.ext h2 htt)
      · refine Nat.card_le_card_of_injective (fun t => (σ t).2.1) fun t t' htt => hσ ?_
        obtain ⟨h1, h2⟩ := k32_dep3_eq_of_c hc₀ (hdep' t) (hdep' t') htt
        exact Prod.ext h1 (Prod.ext htt h2)
    · refine Nat.card_le_card_of_injective (fun t => (σ t).1) fun t t' htt => hσ ?_
      obtain ⟨h1, h2⟩ := k32_dep3_eq_of_b hb₀ (hdep' t) (hdep' t') htt
      exact Prod.ext htt (Prod.ext h1 h2)


end Setup

end CFSG.QuasithinUnique.DoubleA3
